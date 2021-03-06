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
Require Export Equalities.
Import Lia.
(*Require Export Utils. *)

Require Import Serializable.
From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.
Require Import CLIPrelude.
Require Export CLIUtils.

(** Definition of operations in CL and CLVM and expressions in CL *)

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

Definition Exp_ind'   : forall P : Exp -> Prop,
    (forall (op : Op) (args : list Exp), all P args -> P (OpE op args)) ->
    (forall (l : ObsLabel) (i : Z), P (Obs l i)) ->
    (forall v : Var, P (VarE v)) ->
    (forall f2 : Exp,
        P f2 -> forall (d : nat) (e : Exp), P e -> P (Acc f2 d e)) ->
    forall e : Exp, P e := 
  fun (P : Exp -> Prop)
    (f : forall (op : Op) (args : list Exp), all P args -> P (OpE op args))
    (f0 : forall (l : ObsLabel) (i : Z), P (Obs l i))
    (f1 : forall v : Var, P (VarE v))
    (f2 : forall f2 : Exp,
        P f2 -> forall (d : nat) (e : Exp), P e -> P (Acc f2 d e)) =>
    fix F (e : Exp) : P e :=
    match e as e0 return (P e0) with
    | OpE op args => let fix step es : all P es := 
                        match es with
                        | nil => forall_nil P
                        | e' :: es' => forall_cons P (F e') (step es')
                        end
                    in  f op args (step args)
    | Obs l i => f0 l i
    | VarE v => f1 v
    | Acc f3 d e0 => f2 f3 (F f3) d e0 (F e0)
    end.

Reserved Notation "'E[|' e '|]'" (at level 9).

(** Semantics of operations in CL *)

Definition OpSem (op : Op) (vs : list Val) : option Val :=
  match op with
  | Add => match vs with ([ZVal x; ZVal y ]) => Some (ZVal (x + y)) | _ => None end
  | Sub => match vs with ([ZVal x; ZVal y ]) => Some (ZVal (x - y)) | _ => None end
  | Mult => match vs with ([ZVal x; ZVal y ]) => Some (ZVal (x * y)) | _ => None end
  | Div => match vs with ([ZVal x; ZVal y ]) => Some (ZVal (x / y)) | _ => None end
  | And => match vs with ([BVal x; BVal y ]) => Some (BVal (x && y)) | _ => None end
  | Or => match vs with ([BVal x; BVal y ]) => Some (BVal (x || y)) | _ => None end
  | Less => match vs with ([ZVal x; ZVal y ]) => Some (BVal (x <?  y)) | _ => None end
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

Lemma F_acc_none : forall  (f : Env -> ExtEnv -> option Val ) (env: Env) (ext: ExtEnv) (d: nat),
    Acc_sem (Fsem f env ext) d None = None.
Proof. intros. induction d.
       + reflexivity.
       + cbn. rewrite IHd. reflexivity.
Qed.

(** Semantics of expressions in CL *)
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


(** Denotational semantics of CL contracts *)
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

(** TODO 
Definition of instruction for CLVM expressions
Literals should be refactored into OpE to comply with original semantics *)
Inductive instruction :=
| IPushZ : Z -> instruction
| IPushB : bool -> instruction
| IObs : ObsLabel -> Z -> instruction
| IOp : Op -> instruction
| IAccStart1 : Z -> instruction
| IAccStart2 : instruction
| IAccStep : instruction
| IAccEnd : instruction
| IVar : nat -> instruction.

Definition app3 {A} (a b c : list A) := a ++ b ++ c.
Definition LApp3 {A} := liftM3 (@app3 A).

Fixpoint repeat_app {A} (x : list A) (n: nat ) :=
    match n with
      | O => []
      | S k => x ++ (repeat_app x k)
    end.

(** Compilation of CL expressions to CLVM expressions *)
Fixpoint CompileE (e : Exp) : option (list instruction) :=
  match e with
  | OpE op args => match op with
                  | BLit b => match args with | [] => Some [IPushB b] | _ => None end
                  | ZLit z => match args with | [] => Some [IPushZ z] | _ => None end
                  | Neg => match args with
                          | [exp1] =>
                            do s1 <- CompileE exp1;
                            Some (s1 ++ [IOp Neg])
                          | _ => None end
                  | Not => match args with
                          | [exp1] =>
                            do s1 <- CompileE exp1;
                            Some (s1 ++ [IOp Not])
                          | _ => None end
                  | Cond => match args with
                           | [exp1; exp2; exp3] =>
                             do s1 <- (CompileE exp1);
                             do s2 <- (CompileE exp2);
                             do s3 <- (CompileE exp3);
                             Some (s3 ++ s2 ++ s1 ++ [IOp Cond])
                           | _ => None end
                  | op => match args with
                         | [exp1; exp2] =>
                           do s1 <- CompileE exp1;
                           do s2 <- CompileE exp2;
                           Some ( s2 ++ s1 ++ [IOp op]) | _ => None end
                  end
  | Obs l i => Some [IObs l i]
  | VarE v => Some [IVar (translateVarToNat v)]
  | Acc e1 d e2 => match d with
                  | O => do s2 <- (CompileE e2);
                        Some ([IAccStart1 (Z.of_nat d)] ++ s2)
                  | _ => do s1 <- (CompileE e1);
                        do s2 <- (CompileE e2);
                        Some ([IAccStart1 (Z.of_nat d)] ++ s2 ++ [IAccStart2] ++ (repeat_app (s1 ++ [IAccStep]) (d-1)) ++ s1 ++ [IAccEnd])
                  end
  end.

(** Definition of contract instructions in CLVM *)
Inductive CInstruction :=
| CIZero : CInstruction
| CITransfer : Party -> Party -> Asset -> CInstruction
| CIScale : (list instruction) -> CInstruction
| CIBoth : CInstruction
| CITranslate : nat -> CInstruction
| CITranslateEnd : nat ->  CInstruction
| CILet : list instruction -> CInstruction
| CILetEnd : CInstruction
| CIIf : list instruction -> nat -> CInstruction
| CIThen : CInstruction
| CIIfEnd : CInstruction.

(** Compilation of CL contracts to CLVM contracts *)
Fixpoint CompileC (c : Contr) : option (list CInstruction) :=
  match c with
  | Zero => Some [CIZero]
  | Transfer p1 p2 a => Some [CITransfer p1 p2 a]
  | Scale e c => do es <- CompileE e;
                do s <- CompileC c;
                Some (s ++  [CIScale (es)])
  | Both c1 c2 => do s1 <- CompileC c1;
                 do s2 <- CompileC c2;
                 Some (s2 ++ s1 ++ [CIBoth] )
  | Translate n c1 => do s <- (CompileC c1) ;                                    
                     (Some ([CITranslate n] ++ s ++ [CITranslateEnd n]))
  | If e n c1 c2 => do es <- CompileE e;
                   do s1 <- CompileC c1;
                   do s2 <- CompileC c2;
                   Some ([CIIf es n] ++ s2 ++ [CIThen] ++ s1 ++ [CIIfEnd])
  | Let e c => do es <- CompileE e;
              do s <- CompileC c;
              Some ([CILet es] ++ s ++ [CILetEnd])
  end.

Definition pop (l : list (Env -> ExtMap -> option Val)) (env : Env) (ext : ExtMap) :=
  match l with
  | s1::tl => match (s1 env ext) with
            | Some v1 => Some (v1)
            | _   => None
            end
  | _  => None
  end.

Definition pop2 (l : list (Env -> ExtMap -> option Val)) (env : Env) (ext : ExtMap) :=
  match l with
  | s1::s2::tl => match (s1 env ext) , (s2 env ext) with
               | Some v1, Some v2 => Some (v1, v2)
               | _ , _  => None
               end
  | _  => None
  end.

Definition pop3 (l : list (Env -> ExtMap -> option Val)) (env : Env) (ext : ExtMap) :=
  match l with
  | s1::s2::s3::tl => match (s1 env ext) , (s2 env ext) , (s3 env ext) with
                  | Some v1, Some v2, Some v3 => Some (v1, v2, v3)
                  | _ , _ , _  => None
                  end
  | _  => None
  end.

Definition Fsem_stack {A} (f : Env -> ExtMap -> option A) (env : Env) (ext : ExtMap) 
  := (fun m x => x >>= fun x' =>  f (x' :: env) (adv_map (Z.of_nat m) ext)).

Definition find_default (k : (ObsLabel * Z)) (ext : ExtMap) : Val :=
  match (FMap.find k ext) with
  | None => match k with
           | ((LabZ n),_) => (ZVal 0)
           | ((LabB b),_) => (BVal false)
           end
  | Some v => v
  end.

(** Definition of expression semantics in CLVM, parameters are in reverse polish notation.
    When we don't evaluate partially we can expect the environment to be complete and return
    some default value, this eases proofs by a lot.
 *)
Fixpoint StackEInterp (instrs : list instruction) (stack : list (option Val)) (env: Env) (ext: ExtMap) (partial : bool) : option Val :=
  match instrs with
  | [] => match stack with [val] => val | _ => None end
  | hd::tl =>
    match hd with
    | IPushZ z => StackEInterp tl ((Some (ZVal z))::stack) env ext partial
    | IPushB b => StackEInterp tl ((Some (BVal b))::stack) env ext partial
    | IObs l i => if partial then
                   StackEInterp tl ((FMap.find (l,i) ext)::stack) env ext partial
                 else
                   StackEInterp tl ((Some (find_default (l,i) ext))::stack) env ext partial
    | IOp op => match op with
               | Add => match stack with
                       | (Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                        StackEInterp tl (Some (ZVal (z1 + z2))::tl2) env ext partial
                       | _ => None
                       end
               | Sub => match stack with
                       | (Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                         StackEInterp tl (Some (ZVal (z1 - z2))::tl2) env ext partial
                       | _ => None
                       end
               | Mult => match stack with
                        | (Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                          StackEInterp tl (Some (ZVal (z1 * z2))::tl2) env ext partial
                        | _ => None
                        end
               | Div => match stack with
                       | (Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                        StackEInterp tl (Some (ZVal (z1 / z2))::tl2) env ext partial
                       | _ => None
                       end
               | And => match stack with (Some (BVal b1))::(Some (BVal b2))::tl2 =>
                                        StackEInterp tl (Some (BVal (b1 && b2))::tl2) env ext partial | _ => None
                       end
               | Or => match stack with
                      |(Some (BVal b1))::(Some (BVal b2))::tl2 =>
                       StackEInterp tl (Some (BVal (b1 || b2))::tl2) env ext partial
                      | _ => None
                      end
               | Less => match stack with
                        |(Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                         StackEInterp tl (Some (BVal (z1 <? z2))::tl2) env ext partial
                        | _ => None
                        end
               | Leq => match stack with
                       |(Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                        StackEInterp tl (Some (BVal (z1 <=? z2))::tl2) env ext partial
                       | _ => None
                        end
               | Equal => match stack with
                           | (Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                             StackEInterp tl (Some (BVal (z1 =? z2))::tl2) env ext partial
                           | _ => None
                         end
               | Cond => match stack with
                        | (Some (BVal b))::(Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                          StackEInterp tl ((Some (ZVal (if b then z1 else z2)))::tl2) env ext partial
                        | (Some (BVal b))::(Some (BVal b1))::(Some (BVal b2))::tl2 =>
                          StackEInterp tl ((Some (BVal (if b then b1 else b2)))::tl2) env ext partial
                        | _ => None
                        end
               | Not => match stack with
                       | ((Some (BVal b))::tl2) => StackEInterp tl ((Some (BVal (negb b)))::tl2) env ext partial
                       | _ => None end
               | Neg => match stack with
                       | ((Some (ZVal z))::tl2) => StackEInterp tl ((Some (ZVal (0 -z)))::tl2) env ext partial
                       | _ => None end
               | _ => None 
               end
    | IVar n => do v <- (StackLookupEnv n env); StackEInterp tl ((Some v)::stack) env ext partial
    | IAccStart1 z => StackEInterp tl stack env (adv_map (-z) ext) partial
    | IAccStart2 => match stack with (Some v)::tl2 => StackEInterp tl tl2 (v::env) (adv_map 1 ext) partial | _ => None end
    | IAccStep => match stack with (Some v)::tl2 => let env' := List.tl env in
                                                 StackEInterp tl tl2 (v::env') (adv_map 1 ext) partial | _ => None end
    | IAccEnd => StackEInterp tl stack (List.tl env) ext partial
    end
  end.

Fixpoint stack_within_sem  (expis : list instruction) (i : nat)  (env : Env) (rc : ExtMap) (partial : bool) : option (bool * nat)
  := match StackEInterp expis [] env rc partial with
     | Some (BVal true) => Some (true, i)
     | Some (BVal false) => match i with
                            | O => Some (false, i)
                            | S j => stack_within_sem expis j env (adv_map 1 rc) partial
                            end
     | _ => None
     end.


(** Definition of semantics for CLVM *)
Fixpoint StackCInterp (instrs : list CInstruction) (stack : list (option TraceM))
         (env : Env) (exts: list ExtMap) (w_stack : list nat) (bf : nat): option TraceM :=
  match instrs with
  | [] => match stack with [res] => res | _ => None end
  | hd::tl =>
      match hd with
      | CIZero => match bf with
                 | O => StackCInterp tl ((Some empty_traceM)::stack) env exts w_stack bf
                 | _ => StackCInterp tl stack env exts w_stack bf
                 end
      | CITransfer p1 p2 c => match bf with
                             | O => StackCInterp tl ((Some (singleton_traceM (singleton_transM p1 p2 c 1)))::stack) env exts w_stack bf
                             | _ => StackCInterp tl stack env exts w_stack bf
                             end
      | CIScale expis => match bf with
                          | O => 
                            match stack with
                            | hd2::tl2 =>
                              do hd2' <- hd2;
                              do et <- hd_error exts;
                              do v <- (StackEInterp expis [] env et false);
                              do z <- toZ v;
                              StackCInterp tl (Some(scale_traceM z hd2')::tl2) env exts w_stack bf
                            | [] => None
                            end
                          | _ => StackCInterp tl stack env exts w_stack bf
                        end
      | CIBoth => match bf with
                 | O =>
                   match stack with
                   | t1::t2::tl2 =>
                     let trace := (liftM2 add_traceM t1 t2) in
                     StackCInterp tl (trace::tl2) env exts w_stack bf
                   | _ => None
                   end
                 | _ => StackCInterp tl stack env exts w_stack bf
                 end
      | CITranslate n => match bf with 
                                 | O => 
                                   do et <- hd_error exts;
                                   let et' := (adv_map (Z.of_nat n) et) in
                                   StackCInterp tl stack env (et'::exts) w_stack bf
                                 | _ => StackCInterp tl stack env exts w_stack bf
                        end
      | CITranslateEnd n => match bf with
                           | O =>
                             match stack with
                             |t::tl2 => match exts with
                                      | et::exts' =>
                                        match t with
                                        | Some t' => let trace := (delay_traceM n t') in
                                                    StackCInterp tl ((Some trace)::tl2) env exts' w_stack bf
                                        | None => StackCInterp tl (None::tl2) env exts' w_stack bf
                                        end
                                      | p_ => None
                                      end
                             | _ => None
                             end
                           | _ => StackCInterp tl stack env exts w_stack bf
                           end
      | CILet expis => match bf with
                      | O =>
                        do et <- hd_error exts;
                        do v <-  (StackEInterp expis [] env et false);
                        StackCInterp tl stack (v::env) exts w_stack bf
                      | _ => StackCInterp tl stack env exts w_stack bf
                      end
      | CILetEnd => match bf with
                   | O => StackCInterp tl stack (List.tl env) exts w_stack bf
                   | _ => StackCInterp tl stack env exts w_stack bf
                   end
      | CIIf expis n => match bf with
                       | O => match exts with | et::exts' =>
                                               match stack_within_sem expis n env et false with
                                               | Some (branch, d_left) => 
                                                 let d_passed := (n - d_left)%nat in
                                                 let et' := adv_map (Z.of_nat d_passed) et in
                                                 StackCInterp tl stack env (et'::exts) (d_passed::w_stack) (if branch then 1 else 0)
                                               | _ => None
                                               end
                                        | _ => None
                             end
                       | bf' => StackCInterp tl stack env exts w_stack (S bf)
                       end
      | CIThen => match bf with
                 | O => StackCInterp tl stack env exts w_stack 1
                 | (S O) => StackCInterp tl stack env exts w_stack O
                 | _ => StackCInterp tl stack env exts w_stack bf
                 end
      | CIIfEnd => match bf with
                  | O => match stack with
                        | t1::tl2 => match w_stack with
                                      | w::w_stack' => 
                                        let d_passed := w in
                                        do t1' <- t1; let trace := delay_traceM d_passed t1' in
                                                     StackCInterp tl ((Some trace)::tl2) env (List.tl exts) w_stack' O
                                      | _ => None
                                      end
                        | _ => None
                        end
                  | (S O) => match stack with
                        | t1::tl2 => match w_stack with
                                   | w::w_stack' => 
                                     let d_passed := w in
                                     do t1' <- t1; let trace := delay_traceM d_passed t1' in
                                                  StackCInterp tl ((Some trace)::tl2) env (List.tl exts) w_stack' O
                                   | _ => None
                                   end
                        | _ => None
                        end
                  | (S bf') => StackCInterp tl stack env exts w_stack bf'
                  end
      end
  end.

(** Partial evaluation CLVM, we assume expressions only evaluate to None when some required observable is not present. 
    Meaning we assume all expressions are well-formed. Whenever an expression returns None we just evaluate to a Empty trace.*)
       
Fixpoint StackCPartial (instrs : list CInstruction) (stack : list (option TraceM))
         (env : Env) (exts: list ExtMap) (w_stack : list nat) (bf : nat) (be: nat) : option TraceM :=
  match instrs with
  | [] => match stack with [res] => res | _ => None end
  | hd::tl =>
      match hd with
      | CIZero => match (bf + be)%nat with
                 | O => StackCPartial tl ((Some empty_traceM)::stack) env exts w_stack bf be
                 | _ => StackCPartial tl stack env exts w_stack bf be
                 end
      | CITransfer p1 p2 c => match (bf + be)%nat with
                             | O => StackCPartial tl ((Some (singleton_traceM (singleton_transM p1 p2 c 1)))::stack) env exts w_stack bf be
                             | _ => StackCPartial tl stack env exts w_stack bf be
                             end
      | CIScale expis => match (bf + be)%nat with
                          | O => 
                            match stack with
                            | t::tl2 =>
                              do t' <- t;
                              do et <- hd_error exts;
                              match do v <- (StackEInterp expis [] env et true); toZ v with
                              | Some z =>  StackCPartial tl (Some(scale_traceM z t')::tl2) env exts w_stack bf be
                              | None => StackCPartial tl (Some (empty_traceM)::tl2) env exts w_stack bf be
                              end
                            | [] => None
                            end
                          | _ => StackCPartial tl stack env exts w_stack bf be
                        end
      | CIBoth => match (bf + be)%nat with
                 | O =>
                   match stack with
                   | t1::t2::tl2 =>
                     let trace := (liftM2 add_traceM t1 t2) in
                     StackCPartial tl (trace::tl2) env exts w_stack bf be
                   | _ => None
                   end
                 | _ => StackCPartial tl stack env exts w_stack bf be
                 end
      | CITranslate n => match (bf + be)%nat with 
                                 | O => 
                                   do et <- hd_error exts;
                                   let et' := (adv_map (Z.of_nat n) et) in
                                   StackCPartial tl stack env (et'::exts) w_stack bf be
                                 | _ => StackCPartial tl stack env exts w_stack bf be
                        end
      | CITranslateEnd n => match (bf + be)%nat with
                           | O =>
                             match stack with
                             |t::tl2 => match exts with
                                      | et::exts' =>
                                        match t with
                                        | Some t' => let trace := (delay_traceM n t') in
                                                    StackCPartial tl ((Some trace)::tl2) env exts' w_stack bf be
                                        | None => StackCPartial tl (None::tl2) env exts' w_stack bf be
                                        end
                                      | _ => None
                                      end
                             | _ => None
                             end
                           | _ => StackCPartial tl stack env exts w_stack bf be
                           end
      | CILet expis => match bf with
                      | O => match be with
                            | O => do et <- hd_error exts;
                                  match (StackEInterp expis [] env et false) with
                                  | Some v => StackCPartial tl stack (v::env) exts w_stack bf be
                                  | None => StackCPartial tl ((Some empty_traceM)::stack) env exts w_stack bf 1
                                  end
                            | _ =>  StackCPartial tl stack env exts w_stack bf (S be)
                            end
                      | _ => StackCPartial tl stack env exts w_stack bf be
                      end
      | CILetEnd => match bf with
                   | O => match be with
                         | O => StackCPartial tl stack (List.tl env) exts w_stack bf be
                         | _ => StackCPartial tl stack env exts w_stack bf (be - 1)
                         end
                   | _ => StackCPartial tl stack env exts w_stack bf be
                   end
      | CIIf expis n => match bf with
                       | O => match be with
                               | O => match exts with | et::exts' =>
                                               match stack_within_sem expis n env et true with
                                               | Some (branch, d_left) => 
                                                 let d_passed := (n - d_left)%nat in
                                                 let et' := adv_map (Z.of_nat d_passed) et in
                                                 StackCPartial tl stack env (et'::exts) (d_passed::w_stack) (if branch then 1 else 0) be
                                               | None => StackCPartial tl ((Some empty_traceM)::stack) env exts w_stack 0 1
                                               end
                                        | _ => None
                                     end
                               | _ => StackCPartial tl stack env exts w_stack bf (S be)
                             end
                       | _ => StackCPartial tl stack env exts w_stack (S bf) be
                       end
      | CIThen => match bf with
                 | O => match be with
                       | O => StackCPartial tl stack env exts w_stack 1 be
                       | _ => StackCPartial tl stack env exts w_stack 0 be
                       end
                 | (S O) => StackCPartial tl stack env exts w_stack O be
                 | _ => StackCPartial tl stack env exts w_stack bf be
                 end
      | CIIfEnd => match bf with
                  | O => match be with
                        | O => match stack with
                              | t1::tl2 => match w_stack with
                                         | w::w_stack' => 
                                           let d_passed := w in
                                           do t1' <- t1; let trace := delay_traceM d_passed t1' in
                                                        StackCPartial tl ((Some trace)::tl2) env (List.tl exts) w_stack' O be
                                         | _ => None
                                         end
                              | _ => None
                              end
                        | _ => StackCPartial tl stack env exts w_stack bf (be - 1)
                        end
                  | (S O) => match stack with
                        | t1::tl2 => match w_stack with
                                      | w::w_stack' => 
                                        let d_passed := w in
                                        do t1' <- t1; let trace := delay_traceM d_passed t1' in
                                                     StackCPartial tl ((Some trace)::tl2) env (List.tl exts) w_stack' O be
                                      | _ => None
                                      end
                        | _ => None
                        end
                  | (S bf') => StackCPartial tl stack env exts w_stack bf' be
                  end
      end
  end.


(** Interfaces for translating CL to CLVM and running CLVM *)
Definition vmE (instrs : list instruction) (env : Env) (ext : ExtMap) : option Val :=
  StackEInterp instrs [] env  ext false.


Lemma TranslateMapSound : forall (extM : ExtMap) (l : ObsLabel) (i : Z) (v: Val),
    FMap.find  (l, i) extM = Some v -> (ExtMap_to_ExtEnv extM) l i = v.
Proof. intros. unfold ExtMap_to_ExtEnv. rewrite H. reflexivity. Qed.


Lemma all_apply'' {A} (P: A -> Prop) (x: A) (xs: list A) :
  all P (x::xs) -> P x /\ (all P xs).
Proof. intros. inversion H. split.
       - apply H2.
       - apply H3.
Qed.
  
Lemma AdvanceMap1 : forall (ext: ExtMap) (d : Z),
    adv_ext d (ExtMap_to_ExtEnv ext)  = ExtMap_to_ExtEnv (adv_map d ext).
Proof.
  intros. unfold ExtMap_to_ExtEnv. unfold adv_ext.
  repeat (apply functional_extensionality; intros).
  rewrite AdvanceMapSound. reflexivity. 
Qed.

                               
Lemma AdvanceMap2 : forall (ext : ExtMap),
    adv_map 0 ext = ext.
Proof. intros. apply (FMap.ext_eq (adv_map 0 ext) ext). intro.
       destruct k. replace (FMap.find (o, z) ext) with (FMap.find (o, (0 + z)) ext).
       symmetry.
       apply AdvanceMapSound.
       replace (0 + z) with (z) by lia. reflexivity.
Qed.  

Lemma AdvanceMap3 : forall (z1 z2: Z) (ext : ExtMap),
    adv_map z2 (adv_map z1 ext) = adv_map (z2 + z1) ext.
Proof. intros. apply FMap.ext_eq. intro. destruct k.
       rewrite <- AdvanceMapSound. rewrite <- AdvanceMapSound.
       replace (z1 + (z2 + z)) with ((z2 + z1) + z) by lia. apply AdvanceMapSound.
Qed.       
  
Lemma AdvanceExt1 : forall (z1 z2: Z) (ext : ExtEnv),
    adv_ext z2 (adv_ext z1 ext) = adv_ext (z2 + z1) ext.
Proof.
  intros. repeat (apply functional_extensionality; intros). unfold adv_ext.
  replace (z1 + (z2 + x0)) with (z2 + z1 + x0) by lia. reflexivity.
Qed.

Lemma AdvanceExt2 : forall (ext : ExtEnv),
    adv_ext 0 ext = ext.
Proof.
  intros. repeat (apply functional_extensionality; intros). unfold adv_ext.
  replace (0 + x0) with x0 by lia. reflexivity.
Qed.


Lemma Arith3:
  forall ds dc : nat, 0%nat = (ds - dc)%nat -> (dc <= ds)%nat -> ds = dc.
Proof.
  intros ds dc H0 H1. lia. Qed.

Lemma AccSemAux : forall  (d2 d1: nat) (e1 e2 : Exp) (env: Env) (ext: ExtEnv) (v : Val) ,
    Acc_sem (Fsem E[| e1|] env ext)  (d1 + d2) (E[| e2|] env ext) = Some v ->
    (exists v2,
    Acc_sem (Fsem E[| e1|] env ext)  (d1) (E[| e2|] env ext) = Some v2).
Proof. intro. induction d2; intros.
       - exists v. replace (d1 + 0 )%nat with d1 in H by lia. apply H.
       - replace (d1 + S d2)%nat with (S(d1 + d2))%nat in H by lia. cbn in *.
         destruct (Acc_sem (Fsem E[| e1|] env ext) (d1 + d2) (E[| e2|] env ext)) eqn:Eq; try discriminate.
         destruct (IHd2 d1 e1 e2 env ext v0). apply Eq. exists x. apply H0.
Qed.    

Lemma AccSound : forall (lefti: nat)
                   (lasti: nat)
                   (ext : ExtMap) (v1 vs: Val) (env: Env) (stack : list (option Val)) (l1 l2 : list instruction)
                   (e1 e2: Exp) 
  ,
    (forall (env : Env) (expis l0 l1 : list instruction) 
      (ext : ExtMap) (stack : list (option Val)) 
       (v : Val),
        expis = l0 ++ l1 ->
        Some l2 = Some l0 ->
        E[| e1|] env (ExtMap_to_ExtEnv ext) = Some v ->
        StackEInterp (l0 ++ l1) stack env ext false =
        StackEInterp l1 (Some v :: stack) env ext false)  -> 
    Acc_sem (Fsem E[|e1 |] env (ExtMap_to_ExtEnv ext)) lasti (E[|e2|] env (ExtMap_to_ExtEnv ext)) = Some v1 ->
    Acc_sem (Fsem E[|e1 |] env (ExtMap_to_ExtEnv ext)) (lasti + lefti) (E[|e2|] env (ExtMap_to_ExtEnv ext)) = Some vs  ->
    StackEInterp (repeat_app (l2 ++ [IAccStep]) lefti ++ l2 ++ IAccEnd :: l1)
                 stack (v1 :: env) (adv_map (Z.of_nat (S lasti)) ext) false =
    StackEInterp  (l2 ++ IAccEnd :: l1) stack (vs :: env) (adv_map (Z.of_nat (lefti + (S lasti))) ext) false.
Proof. intro. induction lefti; intros.
       - cbn. replace (lasti + 0)%nat with lasti in H1 by lia. rewrite H0 in H1. inversion H1. reflexivity.
       - cbn. repeat rewrite <- app_assoc.
         replace (lasti + S lefti)%nat with (S lasti + lefti)%nat in H1 by lia.
         destruct (AccSemAux lefti (S lasti) e1 e2 env (ExtMap_to_ExtEnv ext) vs). apply H1.
         inversion H2.
         cbn in H4. rewrite H0 in H4. 
         rewrite H with (expis := (l2 ++ [IAccStep] ++ repeat_app (l2 ++ [IAccStep]) lefti ++ l2 ++ IAccEnd :: l1)) (v:=x).
         cbn. repeat rewrite AdvanceMap3.
         replace (1 + Z.of_nat (S lasti)) with (Z.of_nat (S (S lasti))) by lia.
         replace (Z.of_nat (S (lefti + S lasti))) with ((Z.of_nat (S lefti + S lasti))) by lia.
         rewrite IHlefti with (vs:=vs) (e1 := e1) (e2 := e2).
         + replace (S lefti + S lasti)%nat with (lefti + S (S lasti))%nat by lia. reflexivity.
         + apply H.
         + apply H2.
         + apply H1.
         + reflexivity.
         + reflexivity.
         + rewrite AdvanceMap1 in H4. apply H4.
Qed.

Lemma TranslateExpressionStep : forall (e : Exp) (env : Env)  (expis l0 l1 : list instruction)
                                 (ext : ExtMap)  (stack : list (option Val)) (v : Val),
    expis = l0 ++ l1 ->
    CompileE e = Some l0 ->
    Esem e env (ExtMap_to_ExtEnv ext) = Some v -> 
    StackEInterp (l0 ++ l1) stack env ext false =
    StackEInterp l1 ((Some v)::stack) env ext false.
Proof. intro. induction e using Exp_ind'; intros.
       - destruct op; inversion H1; try destruct args; try destruct args; try destruct args; try discriminate;
           try (destruct (CompileE e) eqn:Eq1); try discriminate;
           try (destruct (CompileE e0) eqn:Eq2); try discriminate; inversion H4; cbn in *;
           clear H1 ;
             try (apply all_apply'' in H; destruct H);
             try (apply all_apply'' in H1; destruct H1);
             try (repeat (rewrite <- app_assoc));
             try (destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3); try discriminate;
               try (destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4); try discriminate;
                 try (destruct (E[| e1|] env (ExtMap_to_ExtEnv ext)) eqn:Eq5); try discriminate;
             try unfold Monads.pure in H2.
         + destruct v0; try discriminate;  destruct v1; try discriminate.
           rewrite H1 with ( expis := l2 ++ l ++ [IOp Add] ++ l1) (v :=  ((ZVal z0))); try reflexivity.
           rewrite H with (expis := (l ++ [IOp Add] ++ l1)) (v := (ZVal z)); try reflexivity.
           cbn. rewrite <- H2. reflexivity.  apply Eq1. apply Eq3. apply Eq2. apply Eq4. 
         + destruct v0; try discriminate;  destruct v1; try discriminate.
           rewrite H1 with ( expis := l2 ++ l ++ [IOp Sub] ++ l1) (v :=  ((ZVal z0))); try reflexivity.
           rewrite H with (expis := (l ++ [IOp Sub] ++ l1)) (v := (ZVal z)); try reflexivity.
           cbn. rewrite <- H2. reflexivity.  apply Eq1. apply Eq3. apply Eq2. apply Eq4.
         + destruct v0; try discriminate;  destruct v1; try discriminate.
           rewrite H1 with ( expis := l2 ++ l ++ [IOp Mult] ++ l1) (v :=  ((ZVal z0))); try reflexivity.
           rewrite H with (expis := (l ++ [IOp Mult] ++ l1)) (v := (ZVal z)); try reflexivity.
           cbn. rewrite <- H2. reflexivity.  apply Eq1. apply Eq3. apply Eq2. apply Eq4.
         + destruct v0; try discriminate;  destruct v1; try discriminate.
           rewrite H1 with ( expis := l2 ++ l ++ [IOp Div] ++ l1) (v :=  ((ZVal z0))); try reflexivity.
           rewrite H with (expis := (l ++ [IOp Div] ++ l1)) (v := (ZVal z)); try reflexivity.
           cbn. rewrite <- H2. reflexivity.  apply Eq1. apply Eq3. apply Eq2. apply Eq4.
         + destruct v0; try discriminate;  destruct v1; try discriminate.
           rewrite H1 with ( expis := l2 ++ l ++ [IOp And] ++ l1) (v :=  ((BVal b0))); try reflexivity.
           rewrite H with (expis := (l ++ [IOp And] ++ l1)) (v := (BVal b)); try reflexivity.
           cbn. rewrite <- H2. reflexivity.  apply Eq1. apply Eq3. apply Eq2. apply Eq4.
         + destruct v0; try discriminate;  destruct v1; try discriminate.
           rewrite H1 with ( expis := l2 ++ l ++ [IOp Or] ++ l1) (v :=  ((BVal b0))); try reflexivity.
           rewrite H with (expis := (l ++ [IOp Or] ++ l1)) (v := (BVal b)); try reflexivity.
           cbn. rewrite <- H2. reflexivity.  apply Eq1. apply Eq3. apply Eq2. apply Eq4.
         + destruct v0; try discriminate;  destruct v1; try discriminate.
           rewrite H1 with ( expis := l2 ++ l ++ [IOp Less] ++ l1) (v :=  ((ZVal z0))); try reflexivity.
           rewrite H with (expis := (l ++ [IOp Less] ++ l1)) (v := (ZVal z)); try reflexivity.
           cbn. rewrite <- H2. reflexivity.  apply Eq1. apply Eq3. apply Eq2. apply Eq4.
         + destruct v0; try discriminate;  destruct v1; try discriminate.
           rewrite H1 with ( expis := l2 ++ l ++ [IOp Leq] ++ l1) (v :=  ((ZVal z0))); try reflexivity.
           rewrite H with (expis := (l ++ [IOp Leq] ++ l1)) (v := (ZVal z)); try reflexivity.
           cbn. rewrite <- H2. reflexivity.  apply Eq1. apply Eq3. apply Eq2. apply Eq4.
         + destruct v0; try discriminate;  destruct v1; try discriminate.
           rewrite H1 with ( expis := l2 ++ l ++ [IOp Equal] ++ l1) (v :=  ((ZVal z0))); try reflexivity.
           rewrite H with (expis := (l ++ [IOp Equal] ++ l1)) (v := (ZVal z)); try reflexivity.
           cbn. rewrite <- H2. reflexivity.  apply Eq1. apply Eq3. apply Eq2. apply Eq4.
         + destruct v0; try discriminate.
           rewrite H with (expis := (l ++ [IOp Not] ++ l1)) (v := (BVal b)); try reflexivity.
           rewrite <- H2. reflexivity. apply Eq1. apply Eq3.
         + destruct v0; try discriminate.
           rewrite H with (expis := (l ++ [IOp Neg] ++ l1)) (v := (ZVal z)); try reflexivity.
           rewrite <- H2. reflexivity. apply Eq1. apply Eq3.
         + rewrite H2. reflexivity.
         + inversion H2. reflexivity.
         + destruct (CompileE e1) eqn:Eq6; try discriminate; destruct (sequence
                 (map (fun e : Exp => E[| e|] env (ExtMap_to_ExtEnv ext))
                      args)). destruct args; try discriminate.
           destruct (l4). try discriminate; destruct v2; try discriminate; destruct v1;
             try discriminate; destruct v0 eqn:Eqv0; try discriminate. inversion H2.
           inversion H4.  try (apply all_apply'' in H3; destruct H3).
           repeat (rewrite <- app_assoc).
           rewrite H3 with (expis := l3 ++ l2 ++ l ++ [IOp Cond] ++ l1) (v := (BVal b));try reflexivity.
           rewrite H1 with (expis := l2 ++ l ++ [IOp Cond] ++ l1) (v := (BVal b0));try reflexivity.
           rewrite H with (expis := l ++ [IOp Cond] ++ l1) (v := (BVal b1));try reflexivity.
           apply Eq1. apply Eq3. apply Eq2. apply Eq4. apply Eq6. apply Eq5.
           inversion H2.
           inversion H4.  try (apply all_apply'' in H3; destruct H3).
           repeat (rewrite <- app_assoc).
           rewrite H3 with (expis := l3 ++ l2 ++ l ++ [IOp Cond] ++ l1) (v := (ZVal z));try reflexivity.
           rewrite H1 with (expis := l2 ++ l ++ [IOp Cond] ++ l1) (v := (ZVal z0));try reflexivity.
           rewrite H with (expis := l ++ [IOp Cond] ++ l1) (v := (BVal b));try reflexivity.
           cbn.
           apply Eq1. apply Eq3. apply Eq2. apply Eq4. apply Eq6. apply Eq5.
           destruct v0; destruct v1; destruct v2; discriminate. discriminate.
           destruct args; discriminate. destruct args; discriminate.
         + destruct args; discriminate.
         + destruct args; discriminate.
         + destruct args; discriminate.
       - inversion H0. inversion H1. cbn. unfold ExtMap_to_ExtEnv. unfold find_default.
         reflexivity.
       - inversion H0. inversion H1. cbn in *. rewrite <- lookupTranslateSound. rewrite H4. reflexivity.
       - destruct d. cbn in *.
         + destruct (CompileE e2) eqn:Eq2; try discriminate. inversion H0.
           cbn in *.
         destruct ((E[| e2|] env (adv_ext (- Z.of_nat 0) (ExtMap_to_ExtEnv ext)))) eqn:Eq3.
         rewrite IHe2 with (expis :=  (l ++ l1))
                           (ext := (adv_map (- Z.of_nat 0) ext)) (v := v0); try reflexivity.
           * cbn in *. rewrite H1. cbn. unfold Z.of_nat. rewrite Z.opp_0. rewrite AdvanceMap2. reflexivity. 
           * rewrite AdvanceMap1 in Eq3. apply Eq3.
           * discriminate.
         + inversion H0. destruct (CompileE e2) eqn:Eq2; try discriminate. destruct (CompileE e1) eqn:Eq1; try discriminate.
           inversion H3. clear H3. cbn. clear H0. repeat (rewrite <- app_assoc).
           destruct (E[| e2|] env (adv_ext (- Z.of_nat (S d)) (ExtMap_to_ExtEnv ext))) eqn:EqE2.
           rewrite IHe2 with (expis :=  (l ++ IAccStart2 :: (repeat_app (l2 ++ [IAccStep]) (d - 0) ++ l2 ++ [IAccEnd]) ++ l1)) (v:=v0).
           cbn. replace (d-0)%nat with d by lia. rewrite <- app_assoc.
           destruct d.
           * cbn in *. rewrite EqE2 in H1. rewrite <- app_assoc. rewrite IHe1 with (expis:= (l2 ++ [IAccEnd] ++ l1)) (v:=v). cbn. 
             unfold Z.of_nat. cbn. rewrite AdvanceMap3. replace (1 + - (1)) with (0) by lia.
             rewrite AdvanceMap2. reflexivity.
             reflexivity. reflexivity. repeat rewrite <- AdvanceMap1. auto. 
           * rewrite AdvanceMap3. replace ( (1 + - Z.of_nat (S (S d)))) with (- Z.of_nat (S d)) by lia.
             cbn. repeat rewrite <- app_assoc.
             destruct (E[| e1|] (v0 :: env) (adv_ext (- Z.of_nat (S d)) (ExtMap_to_ExtEnv ext))) eqn:EqE1.
             rewrite IHe1 with (expis := (l2 ++ [IAccStep] ++ repeat_app (l2 ++ [IAccStep]) d ++ l2 ++ [IAccEnd] ++ l1)) (v := v1).
             cbn. rewrite AdvanceMap3. replace (1 + - Z.of_nat (S d)) with (- Z.of_nat d) by lia.
             remember (adv_map (- Z.of_nat (S (S d))) ext) as ext' eqn:EqExt'.
             assert (H5: Acc_sem (Fsem E[|e1 |] env (ExtMap_to_ExtEnv ext')) 1 (E[|e2|] env (ExtMap_to_ExtEnv ext')) = Some v1).
             cbn. rewrite EqExt'. repeat rewrite <- AdvanceMap1. rewrite EqE2. rewrite AdvanceExt1.
             replace (Z.of_nat 1 + - Z.of_nat (S (S d))) with (- Z.of_nat (S d)) by lia.
             rewrite EqE1. reflexivity.
             assert (H6: Acc_sem (Fsem E[|e1 |] env (ExtMap_to_ExtEnv ext')) (2 + d) (E[|e2|] env (ExtMap_to_ExtEnv ext')) = Some v).
             cbn. cbn in H1. rewrite EqExt'. repeat rewrite <- AdvanceMap1. apply H1.
             replace (2 + d)%nat with ((1 + d) + 1)%nat in H6 by lia. apply AccSemAux in H6. destruct H6.
             replace (adv_map (- Z.of_nat d) ext) with (adv_map (Z.of_nat (S 1)) ext').
             rewrite AccSound with (vs:=x) (e1:=e1) (e2:=e2).
             cbn in H1. cbn in H0. rewrite EqExt' in H0. repeat rewrite <- AdvanceMap1 in H0. rewrite H0 in H1.
             rewrite AdvanceExt1 in H1. replace (Z.of_nat (S (S d)) + - Z.of_nat (S (S d))) with 0 in H1 by lia.
             rewrite AdvanceExt2 in H1. rewrite EqExt'. rewrite AdvanceMap3.
             replace (Z.of_nat (d + 2) + - Z.of_nat (S (S d))) with 0 by lia. rewrite AdvanceMap2.
             rewrite IHe1 with (expis := (l2 ++ IAccEnd :: l1)) (v:=v); auto.
             apply IHe1. apply H5. apply H0. rewrite EqExt'. rewrite AdvanceMap3.
             replace (Z.of_nat 2 + - Z.of_nat (S (S d))) with (- Z.of_nat d) by lia. reflexivity.
             reflexivity. reflexivity. rewrite <- AdvanceMap1. apply EqE1.
             remember (adv_map (- Z.of_nat (S (S d))) ext) as ext' eqn:EqExt'.
             assert (H6: Acc_sem (Fsem E[|e1 |] env (ExtMap_to_ExtEnv ext')) (2 + d) (E[|e2|] env (ExtMap_to_ExtEnv ext')) = Some v).
             cbn. cbn in H1. rewrite EqExt'. repeat rewrite <- AdvanceMap1. apply H1.
             replace (2 + d)%nat with (1 + (d + 1))%nat in H6 by lia. apply AccSemAux in H6. destruct H6.
             cbn in H0. rewrite EqExt' in H0. repeat rewrite <-  AdvanceMap1 in H0. rewrite EqE2 in H0.
             rewrite AdvanceExt1 in H0. replace (Z.of_nat 1 + - Z.of_nat (S (S d))) with ((- Z.of_nat (S d))) in H0 by lia.
             rewrite EqE1 in H0. discriminate.
           * reflexivity.
           * reflexivity.
           * rewrite AdvanceMap1 in EqE2. apply EqE2.
           * remember (adv_map (- Z.of_nat (S d)) ext) as ext' eqn:EqExt'.
             assert (H6: Acc_sem (Fsem E[|e1 |] env (ExtMap_to_ExtEnv ext')) (1 + d) (E[|e2|] env (ExtMap_to_ExtEnv ext')) = Some v).
             cbn. cbn in H1. rewrite EqExt'. repeat rewrite <- AdvanceMap1. apply H1.
             replace (1 + d)%nat with (0 + (d + 1))%nat in H6 by lia. apply AccSemAux in H6. destruct H6.
              cbn in H0. rewrite EqExt' in H0. rewrite AdvanceMap1 in EqE2. rewrite EqE2 in H0. discriminate.
           * destruct (CompileE e1); try discriminate.
Qed.

Lemma AccSoundNone : forall (lefti: nat)
                       (lasti: nat)
                       (ext : ExtMap) (v1 : Val) (env: Env) (stack : list (option Val)) (l1 l2 : list instruction)
                       (e1 e2: Exp) 
  ,
    CompileE e1 = Some l2 ->
    (forall (env : Env) (l0 l1 : list instruction)
       (ext : ExtMap) (stack : list (option Val)),
        Some l2 = Some l0 ->
        E[| e1|] env (ExtMap_to_ExtEnv ext) = None ->
        StackEInterp (l0 ++ l1) stack env ext false = None)  -> 
    Acc_sem (Fsem E[|e1 |] env (ExtMap_to_ExtEnv ext)) lasti (E[|e2|] env (ExtMap_to_ExtEnv ext)) = Some v1 ->
    Acc_sem (Fsem E[|e1 |] env (ExtMap_to_ExtEnv ext)) (lasti + lefti) (E[|e2|] env (ExtMap_to_ExtEnv ext)) = None  ->
    StackEInterp (repeat_app (l2 ++ [IAccStep]) lefti ++ l2 ++ IAccEnd :: l1)
                 stack (v1 :: env) (adv_map (Z.of_nat (S lasti)) ext) false = None.
Proof.
  intro. induction lefti; intros.
  - cbn in *. replace (lasti + 0)%nat with lasti in H2 by lia. rewrite H1 in H2. discriminate.
  - cbn. repeat rewrite <- app_assoc.
    destruct (Acc_sem (Fsem E[| e1|] env (ExtMap_to_ExtEnv ext)) (S lasti) (E[| e2|] env (ExtMap_to_ExtEnv ext))) eqn:Eq1.
    + inversion Eq1. cbn in H4.  rewrite H1 in H4.
      rewrite TranslateExpressionStep with (e:=e1) (v:=v) (expis := (l2 ++ [IAccStep] ++ repeat_app (l2 ++ [IAccStep]) lefti ++ l2 ++ IAccEnd :: l1)). cbn. replace (lasti + S lefti)%nat with (S lasti + lefti)%nat in H2 by lia.
      rewrite AdvanceMap3. replace (1 + Z.of_nat (S lasti)) with (Z.of_nat (S (S lasti))) by lia.
      rewrite IHlefti with (e1:=e1) (e2:=e2); auto. reflexivity.
      apply H. rewrite AdvanceMap1 in H4. apply H4.
    + cbn in Eq1. rewrite H1 in Eq1. rewrite H0; auto. rewrite AdvanceMap1 in Eq1. apply Eq1.
Qed.      

Lemma TranslateExpressionNone : forall (e : Exp) (env : Env)  (l0 l1 : list instruction)
                                 (ext : ExtMap)  (stack : list (option Val)),
    CompileE e = Some l0 ->
    Esem e env (ExtMap_to_ExtEnv ext) = None -> 
    StackEInterp (l0 ++ l1) stack env ext false = None.
Proof.
  induction e using Exp_ind'; intros.
  - destruct op; inversion H0; destruct args; inversion H3;
      try (destruct args); try discriminate; try destruct args; try discriminate;
        cbn in *; try (destruct (CompileE e0) eqn:Eq1); try (destruct (CompileE e) eqn:Eq2); try discriminate;
          inversion H3;
          try (apply all_apply'' in H; destruct H);
          try (apply all_apply'' in H2; destruct H2).
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3;
        destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4; cbn in *;
          rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Add]) ++ l1))(v:=v0); auto. 
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e) (expis := l2 ++ [IOp Add] ++ l1) (v:=v); auto. cbn. 
      destruct v; destruct v0; try discriminate; try reflexivity.
      rewrite <- app_assoc. rewrite H2. reflexivity. apply Eq1. apply Eq4. rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Add]) ++ l1)) (v:=v); auto.
      rewrite <- app_assoc. reflexivity.
      rewrite H2. reflexivity. apply Eq1. apply Eq4.
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3;
        destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4; cbn in *;
          rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Sub]) ++ l1))(v:=v0); auto. 
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e) (expis := l2 ++ [IOp Sub] ++ l1) (v:=v); auto. cbn. 
      destruct v; destruct v0; try discriminate; try reflexivity. rewrite H2. reflexivity. apply Eq1.
      apply Eq4. rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Sub]) ++ l1)) (v:=v); auto. 
      rewrite <- app_assoc. rewrite H. reflexivity. apply Eq2. apply Eq3. rewrite H2. reflexivity. apply Eq1. apply Eq4.
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3;
        destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4; cbn in *;
          rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Mult]) ++ l1))(v:=v0); auto. 
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e) (expis := l2 ++ [IOp Mult] ++ l1) (v:=v); auto. cbn. 
      destruct v; destruct v0; try discriminate; try reflexivity. rewrite H2. reflexivity. apply Eq1.
      apply Eq4. rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Mult]) ++ l1)) (v:=v); auto. 
      rewrite <- app_assoc. rewrite H. reflexivity. apply Eq2. apply Eq3. rewrite H2. reflexivity. apply Eq1. apply Eq4.
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3;
        destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4; cbn in *;
          rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Div]) ++ l1))(v:=v0); auto. 
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e) (expis := l2 ++ [IOp Div] ++ l1) (v:=v); auto. cbn. 
      destruct v; destruct v0; try discriminate; try reflexivity. rewrite H2. reflexivity. apply Eq1.
      apply Eq4. rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Div]) ++ l1)) (v:=v); auto. 
      rewrite <- app_assoc. rewrite H. reflexivity. apply Eq2. apply Eq3. rewrite H2. reflexivity. apply Eq1. apply Eq4.
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3;
        destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4; cbn in *;
          rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp And]) ++ l1))(v:=v0); auto. 
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e) (expis := l2 ++ [IOp And] ++ l1) (v:=v); auto. cbn. 
      destruct v; destruct v0; try discriminate; try reflexivity. rewrite H2. reflexivity. apply Eq1.
      apply Eq4. rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp And]) ++ l1)) (v:=v); auto. 
      rewrite <- app_assoc. rewrite H. reflexivity. apply Eq2. apply Eq3. rewrite H2. reflexivity. apply Eq1. apply Eq4.
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3;
        destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4; cbn in *;
          rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Or]) ++ l1))(v:=v0); auto. 
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e) (expis := l2 ++ [IOp Or] ++ l1) (v:=v); auto. cbn. 
      destruct v; destruct v0; try discriminate; try reflexivity. rewrite H2. reflexivity. apply Eq1.
      apply Eq4. rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Or]) ++ l1)) (v:=v); auto. 
      rewrite <- app_assoc. rewrite H. reflexivity. apply Eq2. apply Eq3. rewrite H2. reflexivity. apply Eq1. apply Eq4.
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3;
        destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4; cbn in *;
          rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Less]) ++ l1))(v:=v0); auto. 
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e) (expis := l2 ++ [IOp Less] ++ l1) (v:=v); auto. cbn. 
      destruct v; destruct v0; try discriminate; try reflexivity. rewrite H2. reflexivity. apply Eq1.
      apply Eq4. rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Less]) ++ l1)) (v:=v); auto. 
      rewrite <- app_assoc. rewrite H. reflexivity. apply Eq2. apply Eq3. rewrite H2. reflexivity. apply Eq1. apply Eq4.
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3;
        destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4; cbn in *;
          rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Leq]) ++ l1))(v:=v0); auto. 
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e) (expis := l2 ++ [IOp Leq] ++ l1) (v:=v); auto. cbn. 
      destruct v; destruct v0; try discriminate; try reflexivity. rewrite H2. reflexivity. apply Eq1.
      apply Eq4. rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Leq]) ++ l1)) (v:=v); auto. 
      rewrite <- app_assoc. rewrite H. reflexivity. apply Eq2. apply Eq3. rewrite H2. reflexivity. apply Eq1. apply Eq4.
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3;
        destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4; cbn in *;
          rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Equal]) ++ l1))(v:=v0); auto. 
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e) (expis := l2 ++ [IOp Equal] ++ l1) (v:=v); auto. cbn. 
      destruct v; destruct v0; try discriminate; try reflexivity. rewrite H2. reflexivity. apply Eq1.
      apply Eq4. rewrite TranslateExpressionStep with (e:=e0) (expis := (l ++ (l2 ++ [IOp Equal]) ++ l1)) (v:=v); auto. 
      rewrite <- app_assoc. rewrite H. reflexivity. apply Eq2. apply Eq3. rewrite H2. reflexivity. apply Eq1. apply Eq4.
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3; cbn in *. destruct v; try discriminate.
      rewrite <- app_assoc. rewrite TranslateExpressionStep with (e:=e) (expis:= (l ++ [IOp Not] ++ l1)) (v:=(ZVal z)).
      cbn. reflexivity. reflexivity. apply Eq2. apply Eq3. rewrite <- app_assoc. rewrite H. reflexivity.
      apply Eq2. apply Eq3.
    + destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq3; cbn in *. destruct v; try discriminate.
      rewrite <- app_assoc. rewrite TranslateExpressionStep with (e:=e) (expis:= (l ++ [IOp Neg] ++ l1)) (v:=(BVal b)).
      cbn. reflexivity. reflexivity. apply Eq2. apply Eq3. rewrite <- app_assoc. rewrite H. reflexivity.
      apply Eq2. apply Eq3.
    + destruct args; try discriminate.  try (apply all_apply'' in H6; destruct H6).
      destruct (CompileE e1) eqn:Eq3; try discriminate. inversion H3. cbn.
      destruct (E[| e|] env (ExtMap_to_ExtEnv ext)) eqn:Eq4; destruct (E[| e0|] env (ExtMap_to_ExtEnv ext)) eqn:Eq5;
        destruct (E[| e1|] env (ExtMap_to_ExtEnv ext)) eqn:Eq6; cbn in H1; rewrite <- app_assoc.
      * rewrite TranslateExpressionStep with (e:=e1) (expis := l3 ++ (l ++ l2 ++ [IOp Cond]) ++ l1) (v:=v1); auto.
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := l ++ (l2 ++ [IOp Cond]) ++ l1) (v:=v0); auto.
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e) (expis := l2 ++ [IOp Cond] ++ l1) (v:=v); auto. cbn.
      try destruct v;  try destruct v0; try destruct v1; try discriminate; try reflexivity.
      * rewrite H6; auto.
      * rewrite TranslateExpressionStep with (e:=e1) (expis := l3 ++ (l ++ l2 ++ [IOp Cond]) ++ l1) (v:=v0); auto.
        rewrite <- app_assoc. rewrite H2. reflexivity. apply Eq1. apply Eq5.
      * rewrite H6; auto.
      * rewrite TranslateExpressionStep with (e:=e1) (expis := l3 ++ (l ++ l2 ++ [IOp Cond]) ++ l1) (v:=v0); auto.
      rewrite <- app_assoc.
      rewrite TranslateExpressionStep with (e:=e0) (expis := l ++ (l2 ++ [IOp Cond]) ++ l1) (v:=v); auto.
      rewrite <- app_assoc.
      rewrite H. reflexivity. apply Eq2. apply Eq4.
      * rewrite H6; auto.
      * rewrite TranslateExpressionStep with (e:=e1) (expis := l3 ++ (l ++ l2 ++ [IOp Cond]) ++ l1) (v:=v); auto.
        rewrite <- app_assoc. rewrite H2. reflexivity. apply Eq1. apply Eq5.
      * rewrite H6; auto.
    + destruct args; discriminate.
    + destruct args; discriminate.
    + destruct args; discriminate.
  - inversion H0.
  - inversion H0. inversion H. cbn. rewrite <- lookupTranslateSound. rewrite H2.  reflexivity.
  - inversion H. destruct d.
    + destruct (CompileE e2) eqn:Eq1. inversion H2. cbn.
      cbn in H0. rewrite IHe2. reflexivity. reflexivity. rewrite AdvanceMap1 in H0. apply H0. discriminate.
    + destruct d.
      * cbn in H0. destruct (CompileE e1) eqn:Eq1; destruct (CompileE e2) eqn:Eq2; try discriminate. inversion H2.
        cbn. clear H2. destruct (E[| e2|] env (adv_ext (- Z.of_nat 1) (ExtMap_to_ExtEnv ext))) eqn:Eq3.
        rewrite <- app_assoc.
        rewrite TranslateExpressionStep with (e:=e2) (expis := (l2 ++ (IAccStart2 :: l ++ [IAccEnd]) ++ l1)) (v:=v); auto.
        cbn. rewrite <- app_assoc. apply IHe1; auto. rewrite AdvanceExt1 in H0. rewrite AdvanceMap3.
        rewrite AdvanceMap1 in H0. replace (Z.of_nat 1 + - Z.of_nat 1) with (1 + - Z.of_nat 1) by lia. apply H0.
        rewrite AdvanceMap1 in Eq3. apply Eq3. rewrite <- app_assoc. apply IHe2; auto. rewrite AdvanceMap1 in Eq3. apply Eq3.
      * destruct (CompileE e1) eqn:Eq1; destruct (CompileE e2) eqn:Eq2; try discriminate. inversion H2. cbn.
        rewrite <- app_assoc.
        remember (adv_map (- Z.of_nat (S (S d))) ext) as ext' eqn:EqExt'.
        destruct (Acc_sem (Fsem E[|e1 |] env (ExtMap_to_ExtEnv ext')) 1 (E[|e2|] env (ExtMap_to_ExtEnv ext'))) eqn:Eq3.
        cbn in Eq3. destruct (E[| e2|] env (ExtMap_to_ExtEnv ext')) eqn:Eq4; try discriminate.
        rewrite TranslateExpressionStep with (e:=e2) (expis := (l2 ++ (IAccStart2 :: ((l ++ [IAccStep]) ++ repeat_app (l ++ [IAccStep]) d) ++ l ++ [IAccEnd]) ++ l1)) (v:=v0); auto. cbn. repeat rewrite <- app_assoc.
        rewrite TranslateExpressionStep with (e:=e1) (v:=v) (expis := (l ++ [IAccStep] ++ repeat_app (l ++ [IAccStep]) d ++ l ++ [IAccEnd] ++ l1)); auto.
        cbn. destruct (Acc_sem (Fsem E[|e1 |] env (ExtMap_to_ExtEnv ext')) (S d) (E[|e2|] env (ExtMap_to_ExtEnv ext'))) eqn:Eq6.
        rewrite AdvanceMap3. replace (1 + 1) with (Z.of_nat (S 1)) by lia.
        rewrite AccSound with (vs:=v1) (e1:=e1) (e2:=e2); auto.
        cbn in H0. cbn in Eq6. rewrite EqExt' in Eq6. repeat rewrite <-  AdvanceMap1 in Eq6. rewrite Eq6 in H0.
        rewrite EqExt'. rewrite AdvanceMap3. replace (Z.of_nat (d + 2) + - Z.of_nat (S (S d))) with 0 by lia. rewrite AdvanceMap2.
        rewrite AdvanceExt1 in H0. replace (Z.of_nat (S (S d)) + - Z.of_nat (S (S d))) with 0 in H0 by lia. rewrite AdvanceExt2 in H0.
        rewrite IHe1; auto.
        rewrite <- Eq1. apply TranslateExpressionStep.
        cbn. rewrite Eq4. apply Eq3.
        rewrite AdvanceMap3. replace (1 + 1) with (Z.of_nat 2) by lia.
        rewrite AccSoundNone with (e1:=e1) (e2:=e2); auto. cbn. rewrite Eq4.  apply Eq3. rewrite <- AdvanceMap1. apply Eq3.
        cbn in Eq3. destruct (E[| e2|] env (ExtMap_to_ExtEnv ext')) eqn:Eq4.
        rewrite TranslateExpressionStep with (e:=e2) (expis:= (l2 ++ (IAccStart2 :: ((l ++ [IAccStep]) ++ repeat_app (l ++ [IAccStep]) d) ++ l ++ [IAccEnd]) ++ l1)) (v:=v). cbn. repeat rewrite <- app_assoc. rewrite IHe1; auto.
        rewrite <- AdvanceMap1. apply Eq3. reflexivity. apply Eq2. apply Eq4.
        rewrite IHe2; auto.
Qed.
        
Theorem TranslateExpressionSound : forall (e : Exp) (env : Env) (extM : ExtMap) (expis : list instruction),
    CompileE e = Some expis ->  Esem e env (ExtMap_to_ExtEnv extM) = StackEInterp expis [] env extM false.
Proof.
  intros. unfold vmE. 
  destruct (Esem e env (ExtMap_to_ExtEnv extM)) eqn:Eq.
  - rewrite (app_nil_end expis). rewrite TranslateExpressionStep with (e := e) (expis := (expis ++ [])) (v := v). 
    reflexivity. reflexivity. apply H. apply Eq.
  - rewrite (app_nil_end expis). rewrite TranslateExpressionNone with (e := e). reflexivity. apply H. apply Eq.
Qed.

   
         
Definition vmC (instrs : list CInstruction) (env: Env) (ext: ExtMap) : option TraceM :=
  StackCInterp instrs [] env [ext] [] O.


Definition vmPartial (instrs : list CInstruction) (env: Env) (ext: ExtMap) : option TraceM :=
  StackCPartial instrs [] env [ext] [] 0 0.

Definition CompileRunC (c : Contr) (env : Env) (ext: ExtMap) : option TraceM :=
  do instrs <- (CompileC c) ; vmC instrs env ext.


Definition def_ext : ExtEnv := (fun l i => ZVal 0).
Definition def_extM : ExtMap := FMap.empty.


Definition CompileRunE (e : Exp) : option Val :=
  do ce <- CompileE e; vmE ce [] def_extM.


Definition update_ext (l1 : ObsLabel) (i1 : Z) (vn : Val)  (e : ExtEnv) :=
  (fun l i => if ((OLEq l l1) && (i =? i1))%bool then vn else e l i).

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

Definition option_traceM_to_Trace (t : option TraceM) (default: Z) : option Trace :=
  liftM2 traceMtoTrace t (Some 0).

Lemma empty_TraceM_empty : forall n, FMap.find n empty_traceM = None.
Proof. intro. apply FMap.find_empty. Qed.

Lemma addTraceHelp: forall (tm1 tm2 : TraceM),
    traceMtoTrace (add_traceM tm1 tm2) 0 = add_trace (traceMtoTrace tm1 0) (traceMtoTrace tm2 0).
Proof. intros. unfold traceMtoTrace.
       unfold add_trace. repeat (apply functional_extensionality; intros).
       unfold lookupTraceM. unfold add_trans. unfold add_traceM.
       destruct (FMap.find x (FMap.union_with  (fun trans1 trans2 : TransM => Some (add_transM trans1 trans2)) tm1 tm2)) eqn:Eq.
       - inversion Eq.
         apply fin_maps.lookup_union_with_Some in Eq. destruct Eq; destruct H.
         + rewrite H0. replace (FMap.find x tm1) with (Some t) by H.
           replace (FMap.find x tm2) with (None : option TransM) by H1. cbn. assert (H2: forall n, n + 0 = n) by lia. rewrite H2.
           reflexivity.
         + destruct H. rewrite H0. replace (FMap.find x tm2) with (Some t) by H.
           replace (FMap.find x tm1) with (None : option TransM) by H1. cbn. assert (H2: forall n, 0 + n = n) by lia. rewrite H2.
           reflexivity.
         + destruct H. destruct H. destruct H. destruct H1. rewrite H0. rewrite <- H2. cbn.
           unfold lookup_transM. unfold add_transM. destruct (FMap.find (x0, x1, x2)
                                                                        (FMap.union_with (fun z1 z2 : Z => Some (z1 + z2)) x3 x4)) eqn:Eq.
           replace (FMap.find x tm1) with (Some x3) by H. replace (FMap.find x tm2) with (Some x4) by H1.
           apply fin_maps.lookup_union_with_Some in Eq. destruct Eq. destruct H3.
           replace (FMap.find (x0, x1, x2) x3) with (Some z) by H3.
           replace (FMap.find (x0, x1, x2) x4) with (None : option Z) by H4. lia.
           destruct H3. destruct H3.
           replace (FMap.find (x0, x1, x2) x4) with (Some z) by H4.
           replace (FMap.find (x0, x1, x2) x3) with (None : option Z) by H3. lia.
           destruct H3. destruct H3. destruct H3. destruct H4.
           replace (FMap.find (x0, x1, x2) x3) with (Some x5) by H3.
           replace (FMap.find (x0, x1, x2) x4) with (Some x6) by H4. inversion H5. reflexivity.
           * replace (FMap.find x tm1) with (Some x3) by H.
             replace (FMap.find x tm2) with (Some x4) by H.
             destruct (FMap.find (x0, x1, x2) x3) eqn:Eq1; destruct (FMap.find (x0, x1, x2) x4) eqn:Eq2.
             assert (FMap.find (x0, x1, x2)
                               (FMap.union_with (fun z1 z2 : Z => Some (z1 + z2)) x3 x4) = Some (z + z0)).
             apply fin_maps.lookup_union_with_Some. right. right. exists z. exists z0. split. apply Eq1. split. apply Eq2. reflexivity.
             rewrite H3 in Eq. discriminate.
             assert (FMap.find (x0, x1, x2)
                               (FMap.union_with (fun z1 z2 : Z => Some (z1 + z2)) x3 x4) = Some (z)).
             apply fin_maps.lookup_union_with_Some. left. split. apply Eq1. apply Eq2. rewrite H3 in Eq. discriminate.
             assert (FMap.find (x0, x1, x2)
                               (FMap.union_with (fun z1 z2 : Z => Some (z1 + z2)) x3 x4) = Some (z)).
             apply fin_maps.lookup_union_with_Some. right. left. split. apply Eq1. apply Eq2. rewrite Eq in H3. discriminate.
             lia.
       - cbn. destruct (FMap.find x tm1) eqn:Eq1; destruct (FMap.find x tm2) eqn:Eq2.
         assert (FMap.find x
                           (FMap.union_with
                              (fun trans1 trans2 : TransM =>
                                 Some (add_transM trans1 trans2)) tm1 tm2) = Some (add_transM t t0)).
         apply fin_maps.lookup_union_with_Some. right. right. exists t. exists  t0. split. apply Eq1. split. apply Eq2. reflexivity.
         rewrite H in Eq. discriminate.
         assert (FMap.find x
                           (FMap.union_with
                              (fun trans1 trans2 : TransM =>
                                 Some (add_transM trans1 trans2)) tm1 tm2) = Some t).
         apply fin_maps.lookup_union_with_Some.
         left. split. apply Eq1. apply Eq2. rewrite Eq in H. discriminate.
         assert (FMap.find x
                           (FMap.union_with
                              (fun trans1 trans2 : TransM =>
                                 Some (add_transM trans1 trans2)) tm1 tm2) = Some t).
         apply fin_maps.lookup_union_with_Some. right. left. split. apply Eq1. apply Eq2. rewrite H in Eq. discriminate.
         lia.
Qed.             
           
Lemma addTraceEqual:
      forall (t0 t1 : Trace) (tm1 tm2 : TraceM),
        traceMtoTrace tm1 0 = t0 ->
        traceMtoTrace tm2 0 = t1 ->
        traceMtoTrace (add_traceM tm1 tm2) 0 = add_trace t0 t1.
Proof.
  intros. rewrite <- H. rewrite <- H0. apply addTraceHelp.
Qed.

Lemma SingleTraceEqual:
  forall (p p0 : Party) (a : Asset),
    traceMtoTrace (singleton_traceM (singleton_transM p p0 a 1)) 0 =
    singleton_trace (singleton_trans p p0 a 1).
Proof.  
  intros. unfold singleton_traceM. unfold singleton_transM.
  unfold singleton_trans. unfold traceMtoTrace. unfold singleton_trace.
  repeat (apply functional_extensionality; intros). unfold lookupTraceM.
  destruct (p =? p0)%nat eqn:Eq.
  - cbn. destruct x.
    + assert  (FMap.find 0%nat (FMap.add 0%nat FMap.empty empty_traceM) = Some FMap.empty).
      apply FMap.find_add. rewrite H. unfold lookup_transM.
      replace (FMap.find (x0, x1, x2) FMap.empty) with (None : option Z).
      unfold empty_trans. reflexivity. symmetry. apply FMap.find_empty.
    + assert (H : FMap.find (S x) (FMap.add 0%nat FMap.empty empty_traceM) = FMap.find (S x) empty_traceM).
      apply FMap.find_add_ne. lia. rewrite H. unfold empty_traceM.
      assert (FMap.find (S x) (FMap.empty : TraceM)  = (None : option TransM)).
      apply FMap.find_empty. rewrite H0. unfold empty_trans. reflexivity.
  - cbn. destruct x.
    + assert (FMap.find 0%nat (FMap.add 0%nat (FMap.add (p0, p, a) (- (1)) (FMap.add (p, p0, a) 1 FMap.empty)) empty_traceM) =
              Some (FMap.add (p0, p, a) (- (1)) (FMap.add (p, p0, a) 1 FMap.empty))).
      apply FMap.find_add. rewrite H. unfold lookup_transM.
      destruct (a =? x2)%nat eqn:Eq3. destruct ((p =? x0)%nat) eqn:Eq1; destruct (p0 =? x1)%nat eqn:Eq2.
      * rewrite Nat.eqb_eq in Eq1. rewrite Nat.eqb_eq in Eq2. rewrite Nat.eqb_eq in Eq3.
        rewrite Eq1. rewrite Eq2. rewrite Eq3. cbn.
        assert (FMap.find (x0, x1, x2) (FMap.add (x1, x0, x2) (- (1)) (FMap.add (x0, x1, x2) 1 (FMap.empty : TransM))) =
                FMap.find (x0, x1, x2) (FMap.add (x0, x1, x2) 1 (FMap.empty : TransM))).
        apply FMap.find_add_ne. intro. inversion H0. auto. rewrite Nat.eqb_neq in Eq. rewrite H2 in Eq2. rewrite <- Eq2 in Eq1. auto.
        rewrite H0. assert (H1: FMap.find (x0, x1, x2) (FMap.add (x0, x1, x2) 1 (FMap.empty : TransM)) = Some 1).
        apply FMap.find_add.  rewrite H1. reflexivity.
      * assert ((p0 =? x0)%nat = false). rewrite Nat.eqb_neq. intro. rewrite Nat.eqb_neq in Eq.
        rewrite Nat.eqb_eq in Eq1. rewrite <- H0 in Eq1. auto. rewrite H0. cbn.
        rewrite Bool.andb_comm. cbn. rewrite Nat.eqb_neq in Eq2. rewrite Nat.eqb_neq in H0.
        assert (FMap.find (x0, x1, x2) (FMap.add (p0, p, a) (- (1)) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)))
                = FMap.find (x0, x1, x2) (FMap.add (p, p0, a) 1 (FMap.empty : TransM))).
        apply FMap.find_add_ne. intro. inversion H1. auto. rewrite H1.
        assert (H2 : FMap.find (x0, x1, x2) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)) =
                     FMap.find (x0, x1, x2) (FMap.empty : TransM)).
        apply FMap.find_add_ne. intro.  inversion H2. auto. rewrite H2.
        assert (H3 : FMap.find (x0, x1, x2) (FMap.empty : TransM) = (None : option Z)).
        apply FMap.find_empty. rewrite H3. reflexivity.
      * cbn. assert ((p =? x1)%nat = false). rewrite Nat.eqb_neq. intro. rewrite Nat.eqb_eq in Eq2. rewrite <- Eq2 in H0.
        rewrite Nat.eqb_neq in Eq. auto. rewrite H0. cbn.
        rewrite Nat.eqb_neq in Eq1. rewrite Nat.eqb_neq in H0.
        assert (FMap.find (x0, x1, x2) (FMap.add (p0, p, a) (- (1)) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)))
                = FMap.find (x0, x1, x2) (FMap.add (p, p0, a) 1 (FMap.empty : TransM))).
        apply FMap.find_add_ne. intro. inversion H1. auto. rewrite H1.
        assert (H2 : FMap.find (x0, x1, x2) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)) =
                     FMap.find (x0, x1, x2) (FMap.empty : TransM)).
        apply FMap.find_add_ne. intro. inversion H2. auto. rewrite H2.
        assert (H3 : FMap.find (x0, x1, x2) (FMap.empty : TransM) = (None : option Z)).
        apply FMap.find_empty. rewrite H3. reflexivity.
      * destruct ((p =? x1)%nat) eqn:Eq4. destruct ((p0 =? x0)%nat) eqn:Eq5. cbn.
        { assert (FMap.find (x0, x1, x2) (FMap.add (p0, p, a) (- (1)) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)))
                = Some (-1)).
        rewrite Nat.eqb_eq in Eq3. rewrite Nat.eqb_eq in Eq4. rewrite Nat.eqb_eq in Eq5.
        rewrite Eq3. rewrite Eq4. rewrite Eq5.
        apply FMap.find_add. rewrite H0. lia. }
        { cbn. rewrite Nat.eqb_neq in Eq5.
        assert (FMap.find (x0, x1, x2) (FMap.add (p0, p, a) (- (1)) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)))
                = FMap.find (x0, x1, x2) (FMap.add (p, p0, a) 1 (FMap.empty : TransM))).
        apply FMap.find_add_ne. intro. inversion H0. inversion H0. auto. rewrite H0.
        assert (H2 : FMap.find (x0, x1, x2) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)) =
                     FMap.find (x0, x1, x2) (FMap.empty : TransM)).
        apply FMap.find_add_ne. intro. inversion H1. rewrite Nat.eqb_neq in Eq1. auto. rewrite H2.
        assert (H3 : FMap.find (x0, x1, x2) (FMap.empty : TransM) = (None : option Z)).
        apply FMap.find_empty. rewrite H3. reflexivity. }
        { cbn. rewrite Nat.eqb_neq in Eq4.
          assert (FMap.find (x0, x1, x2) (FMap.add (p0, p, a) (- (1)) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)))
                  = FMap.find (x0, x1, x2) (FMap.add (p, p0, a) 1 (FMap.empty : TransM))).
          apply FMap.find_add_ne. intro. inversion H0. auto. rewrite H0. rewrite Nat.eqb_neq in Eq1.
          assert (H2 : FMap.find (x0, x1, x2) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)) =
                       FMap.find (x0, x1, x2) (FMap.empty : TransM)).
          apply FMap.find_add_ne. intro. inversion H1. auto. rewrite H2.
          assert (H3 : FMap.find (x0, x1, x2) (FMap.empty : TransM) = (None : option Z)).
          apply FMap.find_empty. rewrite H3. reflexivity. }
      * rewrite Bool.andb_comm. replace ((p0 =? x1)%nat && false) with (false && (p0 =? x1)%nat). cbn.
        rewrite Bool.andb_comm. replace ((p0 =? x0)%nat && false) with (false && (p0 =? x0)%nat). cbn.
        rewrite Nat.eqb_neq in Eq3.
        assert (FMap.find (x0, x1, x2) (FMap.add (p0, p, a) (- (1)) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)))
                  = FMap.find (x0, x1, x2) (FMap.add (p, p0, a) 1 (FMap.empty : TransM))).
        apply FMap.find_add_ne. intro. inversion H0. auto. rewrite H0.
        assert (H2 : FMap.find (x0, x1, x2) (FMap.add (p, p0, a) 1 (FMap.empty : TransM)) =
                       FMap.find (x0, x1, x2) (FMap.empty : TransM)).
        apply FMap.find_add_ne. intro. inversion H1. auto. rewrite H2.
        assert (H3 : FMap.find (x0, x1, x2) (FMap.empty : TransM) = (None : option Z)).
        apply FMap.find_empty. rewrite H3. reflexivity.
        apply Bool.andb_comm. apply Bool.andb_comm.
    + assert (FMap.find (S x) (FMap.add 0%nat (FMap.add (p0, p, a) (- (1)) (FMap.add (p, p0, a) 1 FMap.empty)) empty_traceM) =
              FMap.find (S x) (FMap.empty : TraceM)).
      apply FMap.find_add_ne. auto. rewrite H. assert (FMap.find (S x) (FMap.empty : TraceM) = (None : option TransM)).
      apply FMap.find_empty. rewrite H0. unfold empty_trans. reflexivity.
Qed.      


Lemma ScaleEqual:
  forall (z : Z) (x : TraceM),
    traceMtoTrace (scale_traceM z x) 0 = scale_trace z (traceMtoTrace x 0).
Proof.
  intros z x. unfold traceMtoTrace. unfold lookupTraceM.
  repeat (apply functional_extensionality; intro). cbn. unfold scale_trace. unfold scale_trans.
  destruct (FMap.find x0 x) eqn:Eq1.
  - apply ScaleTraceSomeSound with (s := z) in Eq1. rewrite Eq1.
    unfold lookup_transM. destruct (FMap.find (x1, x2, x3) t) eqn:Eq2.
    + apply ScaleTransSomeSound with (s:=z) in Eq2. rewrite Eq2. lia.
    + apply ScaleTransNoneSound with (s:=z) in Eq2. rewrite Eq2. lia.
  - apply ScaleTraceNoneSound with (s:=z) in Eq1. rewrite Eq1. lia.
Qed.

  
Lemma DelayEqual:
  forall (n : nat) (t0 : Trace) (x : TraceM),
    traceMtoTrace x 0 = t0 ->
    traceMtoTrace (delay_traceM n x) 0 = delay_trace n t0.
Proof.
  intros n t0 x H1. rewrite <- H1. unfold traceMtoTrace.
  repeat (apply functional_extensionality; intro). unfold lookupTraceM. unfold delay_trace.
  cbn. destruct (n <=? x0)%nat eqn:Eq1.
  - assert (H: FMap.find x0 (delay_traceM n x) = FMap.find ((x0 - n)%nat) x ).
    rewrite Nat.leb_le in Eq1. 
    assert (x0 = (x0 - n) + n)%nat by lia.
    rewrite H. rewrite <- DelayTraceMSound with (d:=n).
    replace ((x0 - n + n - n)%nat) with (x0 - n)%nat by lia.  reflexivity.
    rewrite H. reflexivity.
  - rewrite Nat.leb_nle in Eq1. assert (n > x0)%nat by lia.
    rewrite DelayTraceMNone. unfold empty_trans. reflexivity.
    apply H.
Qed.
   
Lemma AdvanceExtNeutral : forall (ext : ExtEnv),
    adv_ext 0 ext = ext.
Proof. intro. reflexivity. Qed.

Lemma Stupid:
  forall n : nat, (n - n)%nat = 0%nat.
Proof.
  intros n. induction n. reflexivity. cbn. apply IHn.
Qed.

Lemma Stupid2:
  forall x : nat, (x - 0)%nat = x.
Proof.
  intros x. induction x. cbn. reflexivity. cbn. reflexivity.
Qed.
  
Lemma DelayTraceNeutral:
  forall t : Trace, t = (delay_trace 0 t).
Proof.
  intros t.
  repeat (apply functional_extensionality; intro). unfold delay_trace. cbn. rewrite Stupid2. reflexivity.
Qed.  

Lemma WithinSoundAux : forall (n i : nat) (expis: list instruction) (extM : ExtMap) (env: Env),
    stack_within_sem expis n env extM false = Some (true, i) ->
    (i <= n)%nat.
Proof. 
  intro. induction n; intros. unfold stack_within_sem in H;
            destruct (StackEInterp expis [] env extM false); try discriminate; destruct v;
              try discriminate. destruct b.
  - inversion H. cbn. omega.
  - inversion H.
  - unfold stack_within_sem in H. destruct (StackEInterp expis [] env extM false); try discriminate; destruct v;
              try discriminate. destruct b.
    + inversion H. omega.
    + fold stack_within_sem in H. apply IHn in H. omega.
Qed.

Lemma WithinSoundAux2 : forall (n i : nat) (expis: list instruction) (extM : ExtMap) (env: Env),
    stack_within_sem expis n env extM false = Some (false, i) ->
    (i = 0)%nat.
Proof.
  intro. induction n; intros. unfold stack_within_sem in H;
            destruct (StackEInterp expis [] env extM false); try discriminate; destruct v;
              try discriminate. destruct b. inversion H. inversion H. reflexivity.
  - inversion H. destruct (StackEInterp expis [] env extM false) eqn:Eq1; try discriminate.
    destruct v; try discriminate. destruct b.
    + inversion H1.
    + apply IHn with (expis := expis) (extM := (adv_map 1 extM)) (env := env). apply H1.
Qed.

Lemma ArithAux1:
  forall n i : nat, (i <= n)%nat -> (1 + (n - i))%nat = (S n - i)%nat.
Proof.
  intros n i H2. destruct i; destruct n.
  - cbn. reflexivity.
  - cbn. reflexivity.
  - apply Nat.nle_succ_0 in H2. contradiction.
  - cbn. omega.
Qed.
    
Lemma ArithAux:
  forall n i : nat, (i <= n)%nat -> Z.of_nat (n - i) + 1 = Z.of_nat (S n - i).
Proof.
  intros n i H2.
  assert (H: Z.of_nat (n - i) + 1 = Z.of_nat (1 + (n - i))%nat).
  cbn. induction ((n - i)%nat).
  - reflexivity.
  - lia.
  - rewrite H. rewrite ArithAux1. reflexivity. apply H2.
Qed.

Lemma DelayTraceAux:
  forall (n i : nat) (t : Trace),
    delay_trace n (delay_trace i t) = delay_trace (n + i) t.
Proof.
  intros n i t. unfold delay_trace.
  repeat (apply functional_extensionality; intros).
  destruct ((n <=? x)%nat) eqn:Eq1.
  - rewrite Nat.leb_le in Eq1. destruct (i <=? x - n)%nat eqn:Eq2.
    assert ((n + i <=? x)%nat = true). rewrite Nat.leb_le in Eq2. rewrite Nat.leb_le.
    lia. rewrite H. replace (x - n - i)%nat with (x - (n + i))%nat by lia. reflexivity.
    assert ((n + i <=? x)%nat = false). rewrite Nat.leb_nle. rewrite Nat.leb_nle in Eq2. lia.
    rewrite H. reflexivity.
  - assert ((n + i <=? x)%nat = false). rewrite Nat.leb_nle in Eq1. rewrite Nat.leb_nle. lia.
    rewrite H. reflexivity.
Qed.


Lemma WithinSound : forall  (n i : nat) (expis: list instruction) (extM : ExtMap) (env: Env) (e : Exp) (c1 c2 : Contr),
    CompileE e = Some expis -> 
stack_within_sem expis n env extM false = Some (true, i) ->
within_sem C[| c1|] C[| c2|] e n env (ExtMap_to_ExtEnv extM) =
do v <- C[| c1|] env (adv_ext (Z.of_nat (n - i)) (ExtMap_to_ExtEnv extM));
Some (delay_trace (n - i) v).
Proof.
  intro. induction n; intros.
  - cbn in *. 
    destruct (StackEInterp expis [] env extM false) eqn:Eq1; try discriminate.
    destruct v eqn:Eq2; try discriminate. destruct b eqn:Eq3; try discriminate. inversion H0.
    rewrite <- TranslateExpressionSound with (e := e) in Eq1; auto. rewrite Eq1.
    destruct (C[| c1|] env (ExtMap_to_ExtEnv extM)) eqn:Eq4. unfold Z.of_nat. cbn. rewrite AdvanceExtNeutral.
    rewrite Eq4. rewrite <-  DelayTraceNeutral. reflexivity. cbn. unfold Z.of_nat. rewrite AdvanceExtNeutral.
    rewrite Eq4. reflexivity.    
  - cbn in *. destruct (StackEInterp expis [] env extM false) eqn:Eq1; try discriminate.
    destruct v eqn:E1; try discriminate. destruct b eqn:Eq3.
    + inversion H0.
      rewrite <- TranslateExpressionSound with (e := e) in Eq1; auto. rewrite Eq1. cbn. rewrite Stupid.
      unfold Z.of_nat. rewrite AdvanceExtNeutral. destruct (C[| c1|] env (ExtMap_to_ExtEnv extM)).
      rewrite <- DelayTraceNeutral. reflexivity. reflexivity.
    +  rewrite <- TranslateExpressionSound with (e := e) in Eq1; auto. rewrite Eq1.
       rewrite AdvanceMap1. rewrite IHn with (i := i) (expis := expis).
       * rewrite <- AdvanceMap1. rewrite AdvanceExt1. assert (H2: (i <= n)%nat).
       apply WithinSoundAux with (expis := expis) (extM := adv_map 1 extM) (env := env). apply H0.
       rewrite ArithAux; try apply H2.
       destruct (C[| c1|] env (adv_ext (Z.of_nat (S n - i)) (ExtMap_to_ExtEnv extM))).
       unfold Monads.pure. rewrite DelayTraceAux. rewrite ArithAux1. reflexivity.
       apply H2. reflexivity.
       * apply H.
       * apply H0.
Qed.

Lemma StupidArith:
  forall n : nat, (0 <= n)%nat.
Proof.
  intros n. induction n. reflexivity. cbn. omega.
Qed.
  
Lemma WithinSoundRight : forall  (n i : nat) (expis: list instruction) (extM : ExtMap) (env: Env) (e : Exp) (c1 c2 : Contr),
    CompileE e = Some expis -> 
stack_within_sem expis n env extM false = Some (false, i) ->
within_sem C[| c1|] C[| c2|] e n env (ExtMap_to_ExtEnv extM) =
do v <- C[| c2|] env (adv_ext (Z.of_nat (n - i)) (ExtMap_to_ExtEnv extM));
Some (delay_trace (n - i) v).
Proof.
  intro. induction n; intros.
  - cbn in *.
    destruct (StackEInterp expis [] env extM false) eqn:Eq1; try discriminate.
    destruct v eqn:Eq2; try discriminate. destruct b eqn:Eq3; try discriminate. inversion H0.
    rewrite <- TranslateExpressionSound with (e := e) in Eq1; auto. rewrite Eq1.
    destruct (C[| c2|] env (ExtMap_to_ExtEnv extM)) eqn:Eq4. unfold Z.of_nat. cbn. rewrite AdvanceExtNeutral.
    rewrite Eq4. rewrite <-  DelayTraceNeutral. reflexivity. cbn. unfold Z.of_nat. rewrite AdvanceExtNeutral.
    rewrite Eq4. reflexivity.    
  - cbn in *. destruct (StackEInterp expis [] env extM false) eqn:Eq1; try discriminate.
    destruct v eqn:E1; try discriminate. destruct b eqn:Eq3.
    + inversion H0.
    + rewrite <- TranslateExpressionSound with (e := e) in Eq1; auto. rewrite Eq1.
       rewrite AdvanceMap1. rewrite IHn with (i := i) (expis := expis).
       rewrite <- AdvanceMap1. rewrite AdvanceExt1. assert (H2: (i = 0)%nat).
       apply WithinSoundAux2 with (n:=n) (expis := expis) (extM := adv_map 1 extM) (env := env). apply H0. rewrite H2.
       rewrite ArithAux; try apply H2.
       destruct (C[| c2|] env (adv_ext (Z.of_nat (S n - 0)) (ExtMap_to_ExtEnv extM))).
       unfold Monads.pure. rewrite DelayTraceAux. rewrite ArithAux1. reflexivity.
       apply StupidArith. reflexivity. apply StupidArith. apply H. apply H0.
Qed.

Lemma WithinSoundNone : forall  (n: nat) (expis: list instruction) (extM : ExtMap) (env: Env) (e : Exp) (c1 c2 : Contr),
    CompileE e = Some expis -> 
    stack_within_sem expis n env extM false = None ->
    within_sem C[| c1|] C[| c2|] e n env (ExtMap_to_ExtEnv extM) = None.   
Proof.
  intro. induction n; intros.
  - cbn in *. destruct (StackEInterp expis [] env extM false) eqn:Eq1. rewrite TranslateExpressionSound with (expis := expis).
    rewrite Eq1. destruct (v) eqn:Eq2; try (destruct (b) eqn:Eq3; try discriminate). reflexivity. apply H.
    rewrite TranslateExpressionSound with (expis := expis). rewrite Eq1. reflexivity.
    apply H.
  - cbn in *. destruct (StackEInterp expis [] env extM false) eqn:Eq1; rewrite TranslateExpressionSound with (expis := expis);  try apply H; rewrite Eq1.
    destruct (C[| c1|] env (ExtMap_to_ExtEnv extM)) eqn:Eq2. destruct v; try reflexivity.
    destruct b eqn:Eq3. discriminate. apply IHn with (e:=e) (c1 := c1) (c2 := c2) in H0. rewrite AdvanceMap1.
    rewrite H0. reflexivity.
    apply H. destruct (v); try reflexivity. destruct (b); try reflexivity.
    apply IHn with (e:=e) (c1 := c1) (c2 := c2) in H0. rewrite AdvanceMap1. rewrite H0. reflexivity. apply H.
    reflexivity.
Qed.

Lemma IfAux1:
  forall (c : Contr) (l0 : list CInstruction),
    CompileC c = Some l0 ->
    forall (env : Env)  (extMs : list ExtMap) (bf: nat)
      (l2 : list CInstruction) (stack : list (option TraceM))
      (w_stack : list nat) ,
      StackCInterp (l0 ++ l2) stack env extMs w_stack (S bf) =
      StackCInterp l2 stack env extMs w_stack (S bf).
Proof. intro. induction c; intros; inversion H; try reflexivity.
       - destruct (CompileE e); destruct (CompileC c); try discriminate. inversion H1.
         cbn. rewrite <- app_assoc. rewrite IHc. cbn. reflexivity. reflexivity.
       - destruct (CompileE e); destruct (CompileC c); try discriminate. inversion H1.
         rewrite <- app_assoc. rewrite IHc. cbn. reflexivity. reflexivity.
       - destruct (CompileC c1); destruct (CompileC c2); try discriminate. inversion H1.
         rewrite <- app_assoc. rewrite IHc2; try reflexivity.
         rewrite <- app_assoc. rewrite IHc1; try reflexivity.
       - destruct (CompileC c); try discriminate. inversion H1. cbn.
         rewrite <- app_assoc. rewrite IHc; try reflexivity.
       - destruct (CompileE e); destruct (CompileC c1);
           destruct (CompileC c2); try discriminate. inversion H1. cbn.
         rewrite <- app_assoc. rewrite IHc2. cbn. rewrite <- app_assoc. rewrite IHc1. cbn. reflexivity.
         reflexivity. reflexivity.
Qed.    

Lemma TranslateContractStep : forall (c : Contr) (env : Env) (extM : ExtMap) (extMs : list ExtMap)
                               (l1 l2 : list CInstruction) (stack : list (option TraceM)) (w_stack : list nat),
        CompileC c = Some l1 ->        
        (forall (t: Trace), Csem c env (ExtMap_to_ExtEnv extM) = Some t ->
         exists tm,
           traceMtoTrace tm 0 = t /\ 
           StackCInterp (l1 ++ l2) stack env (extM::extMs) w_stack O = StackCInterp l2 ((Some tm)::stack) env (extM::extMs) w_stack O)
        /\ (Csem c env (ExtMap_to_ExtEnv extM) = None ->
           StackCInterp (l1 ++ l2) stack env (extM::extMs) w_stack O = None).

Proof.
  intro. induction c; intros.
  - split; intros.
    + exists (empty_traceM). split. inversion H0. unfold traceMtoTrace. cbn. repeat (apply functional_extensionality; intro).
    rewrite empty_TraceM_empty. reflexivity. inversion H. cbn. reflexivity.
    + inversion H0.
  - split.   
    + intros. inversion H. destruct (CompileE e) eqn:Eq1; destruct (CompileC c) eqn:Eq2; try discriminate.
      inversion H2. inversion H0. cbn.  rewrite <- TranslateExpressionSound with (e:=e). 
      destruct (E[| e|] env (ExtMap_to_ExtEnv extM)) eqn:Eq3; try discriminate;
        destruct (C[| c|] (v :: env) (ExtMap_to_ExtEnv extM)) eqn:Eq4; try discriminate. rewrite <- app_assoc.
      destruct (IHc (v::env) extM extMs  l0 ([CILetEnd] ++ l2) stack w_stack). reflexivity. 
      destruct (H1 t0). apply Eq4. destruct H6. rewrite H7. exists x. split.
      * inversion H4. rewrite <- H9. apply H6.
      * cbn. reflexivity.
      * apply Eq1.
    + intro. inversion H. destruct (CompileE e) eqn:Eq1; destruct (CompileC c) eqn:Eq2; try discriminate. inversion H2.
      cbn. inversion H0. destruct (E[| e|] env (ExtMap_to_ExtEnv extM)) eqn:Eq3.
      rewrite <- TranslateExpressionSound with (e := e).
      rewrite Eq3. rewrite <- app_assoc. destruct (IHc (v::env) extM extMs l0 ([CILetEnd] ++ l2) stack w_stack). reflexivity.
      rewrite H5. cbn. reflexivity. apply H4. apply Eq1.
      * rewrite <- TranslateExpressionSound with (e:=e).
        rewrite Eq3. reflexivity. apply Eq1.
  - split.
    + inversion H. cbn. inversion H. exists (singleton_traceM (singleton_transM p p0 a 1)).
      split.
      * inversion H0. apply SingleTraceEqual.
      * reflexivity.
    + inversion H. intros. inversion H0.
  - split.  
    + intros. inversion H. destruct (CompileE e) eqn:Eq1; destruct (CompileC c) eqn:Eq2; try discriminate.
    inversion H2. inversion H0.
    destruct (E[| e|] env (ExtMap_to_ExtEnv extM)) eqn:Eq3.
    destruct (C[| c|] env (ExtMap_to_ExtEnv extM)) eqn:Eq4.
    unfold liftM2 in H4. unfold Monads.pure in H4. cbn in H4. destruct (toZ v) eqn:Eq5; try discriminate.
    rewrite <- app_assoc.
    destruct (IHc env extM extMs  l0 ([CIScale l] ++ l2) stack w_stack). reflexivity. destruct (H1 t0). apply Eq4.
    destruct H6. rewrite H7. cbn. rewrite <- TranslateExpressionSound with (e:=e). rewrite Eq3. unfold Monads.pure.
    rewrite Eq5. inversion H4. exists (scale_traceM z x). rewrite <- H6. split.
      * apply ScaleEqual.
      * reflexivity.
      * apply Eq1.
      * cbn in H4. destruct (toZ v); discriminate.
      * inversion H0. rewrite Eq3 in H5. cbn in H5. discriminate.
    + intro. inversion H. destruct (CompileE e) eqn:Eq1; destruct (CompileC c) eqn:Eq2; try discriminate.
      inversion H2. rewrite <- app_assoc. inversion H0.
      destruct (E[| e|] env (ExtMap_to_ExtEnv extM)) eqn:Eq3. 
      destruct (C[| c|] env (ExtMap_to_ExtEnv extM)) eqn:Eq4. 
      cbn in H4. unfold toZ in H4; destruct v; try discriminate.
      clear H4.
      destruct (IHc env extM extMs  l0 ([CIScale l] ++ l2) stack w_stack). reflexivity.
      destruct (H1 t). apply Eq4. destruct H5. rewrite H6. cbn. rewrite <- TranslateExpressionSound with (e:=e). rewrite Eq3.
      cbn. reflexivity. apply Eq1.
      * destruct (IHc env extM extMs  l0 ([CIScale l] ++ l2) stack w_stack). reflexivity.
        rewrite H5. reflexivity. apply Eq4. 
      * destruct (C[| c|] env (ExtMap_to_ExtEnv extM)) eqn:Eq4.
        destruct (IHc env extM extMs  l0 ([CIScale l] ++ l2) stack w_stack). reflexivity.
        destruct (H1 t). apply Eq4. destruct H6.
        rewrite H7. cbn. rewrite <- TranslateExpressionSound with (e:=e). rewrite Eq3. reflexivity. apply Eq1.
        destruct (IHc env extM extMs  l0 ([CIScale l] ++ l2) stack w_stack). reflexivity.
        rewrite H5. cbn. reflexivity. apply Eq4.    
  - inversion H. destruct (CompileC c1)  eqn:Eq1; destruct (CompileC c2) eqn:Eq2; try discriminate.
    inversion H1.
    split; intros; inversion H0; 
    destruct (C[| c1|] env (ExtMap_to_ExtEnv extM)) eqn:Eq3;
    destruct ((C[| c2|] env (ExtMap_to_ExtEnv extM))) eqn:Eq4; try discriminate; repeat (rewrite <- app_assoc).
    + destruct (IHc2 env extM extMs l0 (l ++ [CIBoth] ++ l2) stack w_stack); try reflexivity.
      destruct (H3 t1). apply Eq4. clear H3. clear H5. destruct H6. rewrite H5.
      destruct (IHc1 env extM extMs l ([CIBoth] ++ l2) (Some x ::stack) w_stack); try reflexivity.
      clear H7. destruct (H6 t0). apply Eq3. destruct H7.
      rewrite H8. cbn. unfold Monads.pure. exists (add_traceM x0 x). split. cbn in H4. unfold Monads.pure in H4. inversion H4.
      apply addTraceEqual. apply H7. apply H3. reflexivity.
    + destruct (IHc2 env extM extMs l0 (l ++ [CIBoth] ++ l2) stack w_stack); try reflexivity. clear H3.
      rewrite H5. clear H5.
      destruct (IHc1 env extM extMs l ([CIBoth] ++ l2) (None ::stack) w_stack); try reflexivity. clear H5. apply Eq4.
    + destruct (IHc2 env extM extMs l0 (l ++ [CIBoth] ++ l2) stack w_stack); try reflexivity. clear H5.
      destruct (H3 t). apply Eq4. clear H3. destruct H5. rewrite H5. clear H5.
      destruct (IHc1 env extM extMs l ([CIBoth] ++ l2) (Some x ::stack) w_stack); try reflexivity. clear H5.
      rewrite H6. cbn. reflexivity. apply Eq3.
    + destruct (IHc2 env extM extMs l0 (l ++ [CIBoth] ++ l2) stack w_stack); try reflexivity. clear H3.
      rewrite H5. reflexivity. apply Eq4.
  - inversion H. destruct (CompileC c) eqn:Eq1; try discriminate. inversion H1.
    split; intros; inversion H0; cbn in H4;
      destruct (C[| c|] env (adv_ext (Z.of_nat n) (ExtMap_to_ExtEnv extM))) eqn:Eq2; unfold Monads.pure in H4; inversion H4;
        cbn; rewrite <- app_assoc.
    + destruct (IHc env (adv_map (Z.of_nat n) extM) (extM::extMs)  l ( [CITranslateEnd n] ++ l2) stack w_stack). reflexivity.
      clear H6. destruct (H3 t0). rewrite AdvanceMap1 in Eq2. apply Eq2. destruct H6. rewrite H7. cbn.
      exists (delay_traceM n x). split.
      apply DelayEqual. apply H6.
      * reflexivity.
    + destruct (IHc env (adv_map (Z.of_nat n) extM) (extM::extMs)  l ( [CITranslateEnd n] ++ l2) stack w_stack). reflexivity.
      clear H3. rewrite H5. cbn. reflexivity. rewrite AdvanceMap1 in Eq2. apply Eq2.
  - inversion H. destruct (CompileE e) eqn:Eq1; try discriminate; destruct (CompileC c1) eqn:Eq2; try discriminate;
                   destruct (CompileC c2) eqn:Eq3; try discriminate.
    inversion H1.
    split; intros; inversion H0.
    + cbn. destruct (stack_within_sem l n env extM false) eqn:Eq4.
      destruct (p) eqn:Eq5. destruct b. apply WithinSound with (e := e) (c1 := c1) (c2 := c2) in Eq4.
      rewrite Eq4 in H4. cbn in H4.   
        destruct (C[| c1|] env (adv_ext (Z.of_nat (n - n0)) (ExtMap_to_ExtEnv extM))) eqn:Eq7; try discriminate.
      rewrite <- app_assoc. cbn in Eq4. rewrite (IfAux1 c2). cbn.
      destruct (IHc1 env (adv_map (Z.of_nat (n - n0)) extM) (extM::extMs) l0 ([CIIfEnd] ++ l2) stack
                     (((n - n0)%nat) :: w_stack)). reflexivity.
      clear H5. destruct (H3 t0). rewrite AdvanceMap1 in Eq7. apply Eq7. destruct H5.
      rewrite <- app_assoc.
      rewrite H6. clear H6. clear H3. cbn.
      exists (delay_traceM (n - n0) x). split.
      inversion H4. rewrite <- H5. apply DelayEqual. reflexivity. reflexivity. apply Eq3.
      * apply Eq1.
      * apply WithinSoundRight with (e:=e) (c1 := c1) (c2 := c2) in Eq4. rewrite Eq4 in H4.
        cbn in H4. destruct (C[| c2|] env (adv_ext (Z.of_nat (n - n0)) (ExtMap_to_ExtEnv extM))) eqn:Eq6; try discriminate.
        rewrite <- app_assoc. cbn in Eq4.
        destruct (IHc2 env (adv_map (Z.of_nat (n - n0)) extM) (extM::extMs)  l3 ((CIThen :: l0 ++ [CIIfEnd]) ++ l2) stack
                       ( (n - n0)%nat :: w_stack)). reflexivity. clear H5. destruct (H3 t0).
        rewrite AdvanceMap1 in Eq6. apply Eq6. destruct H5. rewrite H6. cbn. rewrite <- app_assoc. clear H6 H3.
        rewrite (IfAux1 c1). cbn.  inversion H4.
        exists (delay_traceM (n - n0) x). split. apply DelayEqual. apply H5. reflexivity. apply Eq2. apply Eq1. 
      * apply WithinSoundNone with (e:=e) (c1:=c1) (c2:=c2) in Eq4. rewrite H4 in Eq4. discriminate. apply Eq1.
    + cbn. destruct (stack_within_sem l n env extM false) eqn:Eq4.
      destruct (p) eqn:Eq5. destruct b.
      * apply WithinSound with (e := e) (c1 := c1) (c2 := c2) in Eq4. cbn in Eq4.
      rewrite Eq4 in H4. destruct (C[| c1|] env (adv_ext (Z.of_nat (n - n0)) (ExtMap_to_ExtEnv extM))) eqn:Eq6; try discriminate.
      rewrite <- app_assoc. rewrite (IfAux1 c2). cbn.  rewrite <- app_assoc.
      destruct (IHc1 env (adv_map (Z.of_nat (n - n0)) extM) (extM::extMs) l0 ([CIIfEnd] ++ l2) stack ((n - n0)%nat :: w_stack)).
      reflexivity.
      clear H3. rewrite H5. reflexivity. rewrite AdvanceMap1 in Eq6. apply Eq6. apply Eq3. apply Eq1.
      * apply WithinSoundRight with (e := e) (c1 := c1) (c2 := c2) in Eq4. cbn in Eq4.
        rewrite Eq4 in H4. destruct (C[| c2|] env (adv_ext (Z.of_nat (n - n0)) (ExtMap_to_ExtEnv extM))) eqn:Eq6;
                             try discriminate. rewrite <- app_assoc.
        destruct (IHc2 env (adv_map (Z.of_nat (n - n0)) extM) (extM::extMs) l3 ((CIThen :: l0 ++ [CIIfEnd]) ++ l2) stack ((n - n0)%nat :: w_stack)).
        reflexivity. rewrite H5. reflexivity. rewrite AdvanceMap1 in Eq6. apply Eq6. apply Eq1.
      * reflexivity.
Qed.

Theorem TranslateContractSound : forall (c : Contr) (env : Env) (extM : ExtMap) (l : list CInstruction),
    CompileC c = Some l ->
    (forall (t : Trace), Csem c env (ExtMap_to_ExtEnv extM) = Some t ->
                    exists tm, traceMtoTrace tm 0 = t /\
                          vmC l env extM = Some tm)
    /\ (Csem c env (ExtMap_to_ExtEnv extM) = None -> vmC l env extM = None).
  intros. destruct (TranslateContractStep c env extM [] l [] [] []). apply H. split.
  - intros. 
    destruct (H0 t). apply H2. destruct H3. exists x. split.
    apply H3. cbn in H4. rewrite app_nil_r in H4. apply H4.
  - intros. cbn in H1. rewrite app_nil_r in H1. apply H1. apply H2.
Qed.
