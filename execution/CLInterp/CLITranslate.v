Require Import FunctionalExtensionality.
Require Import List.
Import ListNotations.
From Coq Require Import ZArith.
Require Import Basics.
Require Import Automation.
Require Import Monads.
Require Import Blockchain.
Require Import Extras.
Require Import Containers.

Require Import Serializable.
From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.
Require Import CLIPrelude.

Inductive Op : Set := Add | Sub | Mult | Div | And | Or | Less | Leq | Equal |
                      Not | Neg |
                      BLit (b : bool) | ZLit (r : Z) |
                      Cond.

Inductive Exp : Set := OpE (op : Op) (args : list Exp)
                     | Obs (l : ObsLabel) (i : Z)
                     | VarE (v : Var)
                     | Acc (f : Exp) (d : nat) (e : Exp).
Inductive TExpr : Set := Tvar (t : TVar) | Tnum (n : nat).

Inductive Contr : Type :=
| Zero : Contr
| Let : Exp -> Contr -> Contr
| Transfer : Party -> Party -> Asset -> Contr
| Scale : Exp -> Contr -> Contr
| Both : Contr -> Contr -> Contr
| Translate : nat -> Contr -> Contr
| If : Exp -> nat -> Contr -> Contr -> Contr.



Reserved Notation "'E[|' e '|]'" (at level 9).

Definition OpSem (op : Op) (vs : list Val) : option Val :=
  match op with
  | Add => match vs with ([ZVal x; ZVal y ]) => Some (ZVal (x + y)) | _ => None end
  | Sub => match vs with ([ZVal x; ZVal y ]) => Some (ZVal (x - y)) | _ => None end
  | Mult => match vs with ([ZVal x; ZVal y ]) => Some (ZVal (x * y)) | _ => None end
  | Div => match vs with ([ZVal x; ZVal y ]) => Some (ZVal (x / y)) | _ => None end
  | And => match vs with ([BVal x; BVal y ]) => Some (BVal (x && y)) | _ => None end
  | Or => match vs with ([BVal x; BVal y ]) => Some (BVal (x || y)) | _ => None end
  | Less => match vs with ([ZVal x; ZVal y ]) => Some (BVal (x <=?  y)) | _ => None end
  | Leq => match vs with ([ZVal x; ZVal y ]) => Some (BVal ( x <=?  y)) | _ => None end
  | Equal => match vs with ([ZVal x; ZVal y ]) => Some (BVal (x =? y)) | _ => None end
  | BLit b => match vs with ([]) => Some (BVal b) | _ => None end
  | ZLit r => match vs with ([]) => Some (ZVal r) | _ => None end
  | Cond => match vs with
            | ([BVal b; ZVal x; ZVal y ]) => Some (ZVal (if b then x else y))
            | ([BVal b; BVal x; BVal y ]) => Some (BVal (if b then x else y))
            | _ => None end
  | Neg => match vs with ([ZVal x]) => Some (ZVal (0 - x) %Z) | _ => None end
  | Not => match vs with ([BVal x]) => Some (BVal (negb x)) | _ => None end
  end.

Fixpoint Acc_sem {A} (f : nat -> A -> A) (n : nat) (z : A) : A :=
  match n with
  | O => z
  | S n' => f n (Acc_sem f n' z)
  end.


Definition Fsem {A} (f : Env -> ExtEnv -> option A) (env : Env) (ext : ExtEnv) 
  := (fun m x => x >>= fun x' =>  f (x' :: env) (adv_ext (Z.of_nat m) ext)).


Fixpoint Esem (e : Exp) (env : Env) (ext : ExtEnv) : option Val :=
  match e with
  | OpE op args => sequence (map (fun e => E[|e|] env ext) args) >>= OpSem op
  | Obs l i => Some (ext l i)
  | VarE v => lookupEnv v env
  | Acc f l z => let ext' := adv_ext (- Z.of_nat l) ext
                 in Acc_sem (Fsem E[|f|] env ext') l (E[|z|] env ext')
  end
where "'E[|' e '|]'" := (Esem e ).


Definition toZ (v : Val) : option Z := 
  match v with
  | ZVal z => Some z
  | _ => None
  end.

Fixpoint within_sem (c1 c2 : Env -> ExtEnv  -> option Trace) 
         (e : Exp) (i : nat)  (env : Env) (rc : ExtEnv)  : option Trace 
  := match E[|e|] env rc with
     | Some (BVal true) => c1 env rc 
     | Some (BVal false) => match i with
                            | O => c2 env rc
                            | S j => liftM (delay_trace 1) (within_sem c1 c2 e j env (adv_ext 1 rc))
                            end
     | _ => None
     end.

Reserved Notation "'C[|' e '|]'" (at level 9).
Fixpoint Csem (c : Contr) (env : Env) (ext : ExtEnv) : option Trace :=
  match c with
  | Zero => Some empty_trace
  | Let e c => E[|e|] env ext >>= fun val => C[|c|] (val :: env) ext
  | Transfer p1 p2 c => Some (singleton_trace (singleton_trans p1 p2 c 1))
  | Scale e c' => liftM2 scale_trace (E[|e|] env ext >>= toZ) (C[|c'|] env ext)
  | Both c1 c2 => liftM2 add_trace (C[|c1|]env ext) (C[|c2|]env ext)
  | Translate n c1 => liftM (delay_trace n) (C[|c1|] env (adv_ext (Z.of_nat n) ext))
  | If e d c1 c2 => within_sem C[|c1|] C[|c2|] e d env ext 
  end
where "'C[|' e '|]'" := (Csem e).

(** TODO Literals should be refactored into OpE to comply with original semantics *)
Inductive instruction :=
| IPushZ : Z -> instruction
| IPushB : bool -> instruction
| IObs : ObsLabel -> Z -> instruction
| IOp : Op -> instruction
| IAcc : nat -> instruction
| IVar : nat -> instruction.

Definition app3 {A} (a b c : list A) := a ++ b ++ c.
Definition LApp3 {A} := liftM3 (@app3 A).

Fixpoint CompileE (e : Exp) : option (list instruction) :=
  match e with
  | OpE op args => match op with
                   | BLit b => Some [IPushB b]
                   | ZLit z => Some [IPushZ z]
                   | Neg => match args with [exp1] => liftM2 List.app (CompileE exp1) (Some [IOp Neg]) | _ => None end
                   | Not => match args with [exp1] => liftM2 List.app (CompileE exp1) (Some [IOp Not]) | _ => None end
                   | Cond => match args with [exp1; exp2; exp3] => liftM2 List.app (LApp3 (CompileE exp3) (CompileE exp2) (CompileE exp1)) (Some [IOp Cond]) | _ => None end
                   | op => match args with | [exp1; exp2] => LApp3 (CompileE exp2) (CompileE exp1) (Some [IOp op]) | _ => None end
                   end
  | Obs l i => Some [IObs l i]
  | VarE v => Some [IVar (translateVarToNat v)]
  | Acc e1 d e2 => LApp3 (CompileE e2) (CompileE e1) (Some [IAcc d])
  end.


Inductive CInstruction :=
| CIZero : CInstruction
| CITransfer : Party -> Party -> Asset -> CInstruction
| CIScale : (list instruction) -> CInstruction
| CIBoth : CInstruction
| CITranslate : nat -> CInstruction
| CILet : list instruction -> CInstruction
| CIIf : list instruction -> nat -> CInstruction.

Fixpoint CompileC (c : Contr) : option (list CInstruction) :=
  match c with
  | Zero => Some [CIZero]
  | Transfer p1 p2 a => Some [CITransfer p1 p2 a]
  | Scale e c => do es <- CompileE e; liftM2 List.app (CompileC c) (Some [CIScale (es)])
  | Both c1 c2 => LApp3 (CompileC c2) (CompileC c1) (Some [CIBoth])
  | Translate n c1 => liftM2 List.app (CompileC c1) (Some [CITranslate n])
  | If e n c1 c2 => do es <- CompileE e; LApp3 (CompileC c2) (CompileC c1) (Some [CIIf es n])
  | Let e c => do es <- CompileE e; liftM2 List.app (CompileC c) (Some [CILet es] )
  end.

Definition pop (l : list (Env -> ExtMap -> option Val)) (env : Env) (ext : ExtMap) :=
  match l with
  | s1::tl => match (s1 env ext) with
              | Some v1 => Some (v1 , tl)
              | _   => None
              end
  | _  => None
  end.

Definition pop2 (l : list (Env -> ExtMap -> option Val)) (env : Env) (ext : ExtMap) :=
  match l with
  | s1::s2::tl => match (s1 env ext) , (s2 env ext) with
                  | Some v1, Some v2 => Some (v1, v2, tl)
                  | _ , _  => None
                  end
  | _  => None
  end.

Definition pop3 (l : list (Env -> ExtMap -> option Val)) (env : Env) (ext : ExtMap) :=
  match l with
  | s1::s2::s3::tl => match (s1 env ext) , (s2 env ext) , (s3 env ext) with
                      | Some v1, Some v2, Some v3 => Some (v1, v2, v3, tl)
                      | _ , _ , _  => None
                      end
  | _  => None
  end.

Definition Fsem_stack {A} (f : Env -> ExtMap -> option A) (env : Env) (ext : ExtMap) 
  := (fun m x => x >>= fun x' =>  f (x' :: env) (adv_map (Z.of_nat m) ext)).

Definition find_default (k : (ObsLabel * Z)) (ext : ExtMap) (default : Val) : Val := match (FMap.find k ext) with
                                                                                     | None => default
                                                                                     | Some v => v
                                                                                     end.

Fixpoint StackEInterp (instrs : list instruction) (stack : list (Env -> ExtMap -> option Val)) (env: Env) (ext: ExtMap) : option Val :=
  match instrs with
  | [] => match stack with
          | [val] => val env ext
          | _ => None
          end
  | hd::tl => match hd with
              | IPushZ z => StackEInterp tl ((fun e et => Some (ZVal z))::stack) env ext
              | IPushB b => StackEInterp tl ((fun e et => Some (BVal b))::stack) env ext
              | IObs l i => StackEInterp tl ((fun e et => (Some (find_default (l,i) et (ZVal 0))))::stack) env ext
              | IOp op => match op with
                          | Add => match (pop2 stack env ext) with Some ((ZVal z1),(ZVal z2), tl2)
                                                                   => StackEInterp tl ((fun e et => Some (ZVal (z1 + z2)))::tl2) env ext | _ => None end
                          | Sub => match (pop2 stack env ext) with Some ((ZVal z1),(ZVal z2), tl2)
                                                                   => StackEInterp tl ((fun e et => Some (ZVal (z1 - z2)))::tl2) env ext | _ => None end
                          | Mult => match (pop2 stack env ext) with Some ((ZVal z1),(ZVal z2), tl2)
                                                                    => StackEInterp tl ((fun e et => Some (ZVal (z1 * z2)))::tl2) env ext | _ => None end
                          | Div => match (pop2 stack env ext) with Some ((ZVal z1),(ZVal z2), tl2)
                                                                   => StackEInterp tl ((fun e et => Some (ZVal (z1 / z2)))::tl2) env ext | _ => None end
                          | And => match (pop2 stack env ext) with Some ((BVal b1),(BVal b2), tl2)
                                                                   => StackEInterp tl ((fun e et => Some (BVal (b1 && b2)))::tl2) env ext | _ => None end
                          | Or => match (pop2 stack env ext) with Some ((BVal b1),(BVal b2), tl2)
                                                                  => StackEInterp tl ((fun e et => Some (BVal (b1 || b2)))::tl2) env ext | _ => None end
                          | Less => match (pop2 stack env ext) with Some ((ZVal z1),(ZVal z2), tl2)
                                                                    => StackEInterp tl ((fun e et => Some (BVal (z1 <? z2)))::tl2) env ext | _ => None end
                          | Leq => match (pop2 stack env ext) with Some ((ZVal z1),(ZVal z2), tl2)
                                                                   => StackEInterp tl ((fun e et => Some (BVal (z1 <=? z2)))::tl2) env ext | _ => None end
                          | Equal => match (pop2 stack env ext) with Some ((ZVal z1),(ZVal z2), tl2)
                                                                     => StackEInterp tl ((fun e et => Some (BVal (z1 =? z2)))::tl2) env ext | _ => None end
                          | Cond => match (pop3 stack env ext) with
                                    | Some ((BVal b),(ZVal x),(ZVal y),tl2) => let v := if b then x else y in
                                                                               StackEInterp tl ((fun e et => Some (ZVal v))::tl2) env ext
                                    | Some ((BVal b),(BVal x),(BVal y),tl2) => let v := if b then x else y in
                                                                               StackEInterp tl ((fun e et => Some (BVal b))::tl2) env ext
                                    | _ => None end
                          | Neg => match (pop stack env ext) with Some (ZVal x, tl2) => StackEInterp tl ((fun e et => Some (ZVal (0 - x) ))::tl2) env ext | _ => None end
                          | Not => match (pop stack env ext) with Some (BVal b, tl2) => StackEInterp tl ((fun e et => Some (BVal (negb b)))::tl2) env ext | _ => None end
                          | _ => None
                          end
              (** Might need to change this *)
              | IVar n => do v <- (StackLookupEnv n env); StackEInterp tl ((fun e et => Some v)::stack) env ext
              | IAcc n => match stack with
                          | s1::s2::tl2 => StackEInterp tl ((fun e et => let ext' := adv_map (- Z.of_nat n) et
                                                                         in Acc_sem (Fsem_stack s1 env ext') n (s1 env ext)) :: tl2) env ext
                          | _ => None
                          end
              end
  end.

Fixpoint stack_within_sem (c1 c2 : Env -> ExtMap  -> option TraceM) 
         (expis : list instruction) (i : nat)  (env : Env) (rc : ExtMap)  : option TraceM
  := match StackEInterp expis [] env rc with
     | Some (BVal true) => c1 env rc 
     | Some (BVal false) => match i with
                            | O => c2 env rc
                            | S j => liftM (delay_traceM 1) (stack_within_sem c1 c2 expis j env (adv_map 1 rc))
                            end
     | _ => None
     end.

Fixpoint StackCInterp (instrs : list CInstruction) (stack : list (Env -> ExtMap -> option TraceM)) (env : Env) (ext: ExtMap) : option TraceM :=
  match instrs with
  | [] => match stack with [res] => res env ext | _ => None end
  | hd::tl =>
    match hd with
    | CIZero => StackCInterp tl ((fun e et => Some empty_traceM)::stack) env ext
    | CITransfer p1 p2 c => StackCInterp tl ((fun e et => Some(singleton_traceM (singleton_transM p1 p2 c 1)))::stack) env ext
    | CIScale expis => match stack with hd2::tl2 => StackCInterp tl ((fun e et => do z <- liftM toZ (StackEInterp expis [] e et); liftM2 scale_traceM z (hd2 e et))::tl2) env ext
                                   | [] => None
                       end
    | CIBoth => match stack with t1::t2::tl2 => StackCInterp tl ((fun e et => liftM2 add_traceM (t1 e et) (t2 e et))::tl2) env ext | _ => None end 
    | CITranslate n => match stack with t1::tl2 => StackCInterp tl ((fun e et => liftM (delay_traceM n) (t1 e (adv_map (Z.of_nat n) et)))::tl2) env ext | _ => None end
    | CIIf expis n => match stack with t1::t2::tl2 => StackCInterp tl ((fun e et => stack_within_sem t1 t2 expis n e et)::tl2) env ext | _ => None end
    | CILet expis => match stack with t1::tl2
                                      => StackCInterp tl
                                                      ((fun e et => do v <- (StackEInterp expis [] e et);(t1 (v::e) et))::tl2)
                                                      env ext
                                 | _ => None end
    end
  end.



Definition vmE (instrs : list instruction) (env : Env) (ext : ExtMap) : option Val :=
  StackEInterp instrs [] env  ext.

Theorem CompileESound : forall (e : Exp) (env : Env) (extM : ExtMap) (expis : list instruction),
    CompileE e = Some expis ->  Esem e env (ExtMap_to_ExtEnv extM) = vmE expis env extM.
Proof.
  intro.  induction e; intros.
  - Admitted.


Definition vmC (instrs : list CInstruction) (env: Env) (ext: ExtMap) : option TraceM :=
  StackCInterp instrs [] env ext.

Definition CompileRunC (c : Contr) (env : Env) (ext: ExtMap) : option TraceM :=
  do instrs <- (CompileC c) ; vmC instrs env ext.


Definition def_ext : ExtEnv := (fun l i => ZVal 0).
Definition def_extM : ExtMap := FMap.empty.


Definition CompileRunE (e : Exp) : option Val :=
  do ce <- CompileE e; vmE ce [] def_extM.


Definition update_ext (l1 : ObsLabel) (i1 : Z) (vn : Val)  (e : ExtEnv) := (fun l i => if ((OLEq l l1) && (i =? i1))%bool then vn else e l i).

Definition lookupTrace (t : option Trace) (n : nat) (p1 p2 : Party) (a: Asset) : option Z :=
  match t with 
  | Some t => Some (t n p1 p2 a)
  | None => None end
.
Definition lookupTraceM (t : option TraceM) (n : nat) (p1 p2 : Party) (a: Asset) : option Z :=
  match t with 
  | Some t => do trans <- FMap.find n t; lookup_transM p1 p2 a trans
  | None => None end
.

Definition traceMtoTrace (t : TraceM) (default: Z) : Trace :=
  fun n p1 p2 a => match lookupTraceM (Some t) n p1 p2 a with
                | Some z => z
                | None => default
                end.

