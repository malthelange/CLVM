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
Require Export Utils. 

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
                  | BLit b => Some [IPushB b]
                  | ZLit z => Some [IPushZ z]
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
  | Acc e1 d e2 => do s1 <- (CompileE e1);
                  do s2 <- (CompileE e2);
                  Some ([IAccStart1 (Z.of_nat d)] ++ s2 ++ [IAccStart2] ++ (repeat_app (IAccStep::s1) d) ++ [IAccEnd])
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
| CIIf : list instruction -> nat -> CInstruction
| CIIfEnd : CInstruction.

(** Compilation of CL contracts to CLVM contracts *)
Fixpoint CompileC (c : Contr) : option (list CInstruction) :=
  match c with
  | Zero => Some [CIZero]
  | Transfer p1 p2 a => Some [CITransfer p1 p2 a]
  | Scale e c => do es <- CompileE e; liftM2 List.app (CompileC c) (Some [CIScale (es)])
  | Both c1 c2 => LApp3 (CompileC c2) (CompileC c1) (Some [CIBoth])
  | Translate n c1 => do s <- (CompileC c1) ;                                    
                     (Some ([CITranslate n] ++ s ++ [CITranslateEnd n]))
  | If e n c1 c2 => do es <- CompileE e;
                   do s1 <- CompileC c1;
                   do s2 <- CompileC c2;
                   Some ([CIIf es n] ++ s2 ++ s1 ++ [CIIfEnd])
  | Let e c => do es <- CompileE e;
              do s <- CompileC c;
              Some ([CILet es] ++ s)
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

Definition find_default (k : (ObsLabel * Z)) (ext : ExtMap) (default : Val) : Val := match (FMap.find k ext) with
                                                                                     | None => default
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
                   StackEInterp tl ((Some (find_default (l,i) ext (ZVal 0)))::stack) env ext partial
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
    | IVar n => StackEInterp tl ((StackLookupEnv n env)::stack) env ext partial
    | IAccStart1 z => StackEInterp tl stack env (adv_map (0-z) ext) partial
    | IAccStart2 => match stack with (Some v)::tl2 => StackEInterp tl tl2 (v::env) ext partial | _ => None end
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

(** Definition of semantics for CLVM, parameters are in reverse polish notation *)
Fixpoint StackCInterp (instrs : list CInstruction) (stack : list (option TraceM)) (env : Env) (exts: list ExtMap) (w_stack : list (bool * nat)) : option TraceM :=
  match instrs with
  | [] => match stack with [res] => res | _ => None end
  | hd::tl =>
    match hd with
    | CIZero => StackCInterp tl ((Some empty_traceM)::stack) env exts w_stack
    | CITransfer p1 p2 c => StackCInterp tl ((Some (singleton_traceM (singleton_transM p1 p2 c 1)))::stack) env exts w_stack
    | CIScale expis => match stack with
                      | hd2::tl2 =>
                        do et <- hd_error exts;
                        let trace :=
                            (do z <- liftM toZ (StackEInterp expis [] env et false); liftM2 scale_traceM z hd2)
                        in StackCInterp tl (trace::tl2) env exts w_stack
                      | [] => None
                      end
    | CIBoth => match stack with
               | t1::t2::tl2 =>
                 let trace := (liftM2 add_traceM t1 t2) in
                 StackCInterp tl (trace::tl2) env exts w_stack
               | _ => None end
    | CITranslate n  => do et <- hd_error exts;
                       let et' := (adv_map (Z.of_nat n) et) in
                       StackCInterp tl stack env (et'::exts) w_stack
    | CITranslateEnd n => match stack with
                         |t::tl2 => match exts with
                                  | et::exts' =>
                                    do t' <- t;
                                    let trace := (delay_traceM n t') in
                                    StackCInterp tl ((Some trace)::tl2) env exts' w_stack
                                  | p_ => None
                                  end
                         | _ => None
                         end
    | CILet expis => do et <- hd_error exts;
                     do v <- (StackEInterp expis [] env et false);
                       StackCInterp tl stack (v::env) exts w_stack
    | CIIf expis n => match exts with | et::exts' =>
                                       match stack_within_sem expis n env et false with
                                       | Some (branch, d_left) => 
                                         let d_passed := (n - d_left)%nat in
                                         let et' := adv_map (Z.of_nat d_passed) et in
                                         StackCInterp tl stack env (et'::exts') ((branch, d_passed)::w_stack)
                                       | _ => None
                                       end
                                | _ => None
                     end
    | CIIfEnd => match stack with
                | t1::t2::tl2 => match w_stack with
                              | w::w_stack' => 
                                let (branch, d_passed) := w in
                                do t1' <- t1;
                                do t2' <- t2;
                                 let trace := delay_traceM d_passed (if branch then t1' else t2') in
                                 StackCInterp tl ((Some trace)::tl2) env (List.tl exts) w_stack'
                              | _ => None
                              end
                | _ => None
                end
                                 
    end
  end.

(** Partial evaluation CLVM, we assume expressions only evaluate to None when some required observable is not present. 
    Meaning we assume all expressions are well-formed. Whenever an expression returns None we just evaluate to a Empty trace.*)

Fixpoint StackCPartial (instrs : list CInstruction) (stack : list (option TraceM)) (env : Env) (exts: list ExtMap) (w_stack : list (option (bool * nat))) : option TraceM :=
  match instrs with
  | [] => match stack with
         |[res] => res
         | _ => None
         end
  | hd::tl => 
    match hd with
    | CIZero => StackCPartial tl ((Some empty_traceM)::stack) env exts w_stack
    | CITransfer p1 p2 c => let trace := (singleton_traceM (singleton_transM p1 p2 c 1)) in
                           StackCPartial tl ((Some trace)::stack) env exts w_stack
    | CIScale expis => match stack with
                      | hd2::tl2 => do et <- hd_error exts;
                                  match liftM toZ (StackEInterp expis [] env et true) with
                                  | Some z => liftM2 scale_traceM z hd2
                                  | None => (Some empty_traceM)
                                  end
                      | _ => None 
                      end
    | CIBoth => match stack with t1::t2::tl2 =>
                                let trace := (liftM2 add_traceM t1 t2) in
                                StackCPartial tl (trace::tl2) env exts w_stack
                           | _ => None end
    | CITranslate n  => do et <- hd_error exts;
                       let et' := (adv_map (Z.of_nat n) et) in
                       StackCPartial tl stack env (et'::exts) w_stack
    | CITranslateEnd n => match stack  with
                         |t::tl2 => match exts with
                                  | et::exts' =>
                                    do t' <- t;
                                    let trace := (delay_traceM n t') in
                                    StackCPartial tl ((Some trace)::tl2) env exts' w_stack
                                  | p_ => None
                                  end
                         | _ => None
                         end
    | CIIf expis n => match exts with | et::exts' =>
                                       match  stack_within_sem expis n env et false with
                                       | Some (branch, d_left) => 
                                         let d_passed := (n - d_left)%nat in
                                         let et' := adv_map (Z.of_nat d_passed) et in
                                         StackCPartial tl stack env (et'::exts') ((Some (branch, d_passed))::w_stack)
                                       | _ => StackCPartial tl stack env exts ((None)::w_stack)
                                       end
                                | _ => None
                     end
    | CIIfEnd => match stack with
                | t1::t2::tl2 => match w_stack with
                              | (Some w)::w_stack' => 
                                let (branch, d_passed) := w in
                                do t1' <- t1;
                                do t2' <- t2;
                                let trace := delay_traceM d_passed (if branch then t1' else t2') in
                                StackCPartial tl ((Some trace)::tl2) env (List.tl exts) w_stack'
                              | None::w_stack' => StackCPartial tl ((Some empty_traceM)::tl2) env (List.tl exts) w_stack'
                              | _ => None
                              end
                | _ => None
                end
    | CILet expis => do et <- hd_error exts;
                    do v <- (StackEInterp expis [] env et false);
                    StackCPartial tl stack (v::env) exts w_stack
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

(** This is a proof for one case of Op-expressions. In principle i could just copy this 16 times, with a small correction to the asssertion,
    and a the number of destructs for args. But that is way way too messy. So i need some way to refactor this into cleaner steps.
    It might be worth it to look into the CL repository for already existing tactics.
 destruct op. 
         + inversion H1. destruct args. discriminate. destruct args. discriminate. destruct args.
           unfold LApp3 in H4. unfold liftM3 in H4. destruct (CompileE e0) eqn:Eq1. destruct (CompileE e) eqn:Eq2.
           cbn in H4. unfold app3 in H4.  inversion H4. apply all_apply'' in H. destruct H.
           apply all_apply'' in H3. destruct H3. repeat rewrite <-  app_assoc.
           rewrite H3 with (extM := extM) (expis := (l ++ l2 ++ [IOp Add] ++ l1)) (l0 := l)
                           (l1 := l2 ++ [IOp Add] ++ l1) (stack := stack) (env0 := env0)
                           (f := (fun (env1 : Env) (ext2: ExtMap) => E[| e0|] env1 (ExtMap_to_ExtEnv ext2))).
           rewrite H with (extM := extM) (expis := (l2 ++ [IOp Add] ++ l1)) (l0 := l2)
                           (l1 := [IOp Add] ++ l1) (stack := ((fun (env1 : Env) (ext2 : ExtMap) => E[| e0|] env1 (ExtMap_to_ExtEnv ext2)) :: stack)) (env0 := env0)
                           (f := (fun (env1 : Env) (ext2: ExtMap) => E[| e|] env1 (ExtMap_to_ExtEnv ext2))). rewrite <- H2. cbn. assert (H7: (fun (e1 : Env) (et : ExtMap) =>
      match
        match E[| e|] e1 (ExtMap_to_ExtEnv et) with
        | Some v1 =>
            match E[| e0|] e1 (ExtMap_to_ExtEnv et) with
            | Some v2 => Some (v1, v2)
            | None => None
            end
        | None => None
        end
      with
      | Some (ZVal z1, BVal _) => None
      | Some (ZVal z1, ZVal z2) => Some (ZVal (z1 + z2))
      | _ => None
      end) = (fun (env1 : Env) (ext2 : ExtMap) =>
      do x <-
      liftM2 (fun (x' : Val) (xs' : list Val) => x' :: xs')
        (E[| e|] env1 (ExtMap_to_ExtEnv ext2))
        (liftM2 (fun (x' : Val) (xs' : list Val) => x' :: xs')
           (E[| e0|] env1 (ExtMap_to_ExtEnv ext2)) (Some [])); OpSem Add x)).
            repeat (apply functional_extensionality ; intro). 
             destruct (E[| e|] x (ExtMap_to_ExtEnv x0)) eqn:Eq5.
             destruct (E[| e0|] x (ExtMap_to_ExtEnv x0)) eqn:Eq6; reflexivity.
             reflexivity.
             rewrite H7.  reflexivity.
                            apply env. apply extM. reflexivity. apply Eq2. reflexivity. apply env. apply extM. reflexivity.
                            apply Eq1. reflexivity. discriminate. discriminate. discriminate.
*)

  
Lemma AdvanceMap1 : forall (ext: ExtMap) (d : Z),
    adv_ext d (ExtMap_to_ExtEnv ext)  = ExtMap_to_ExtEnv (adv_map d ext).
Proof.
  intros. unfold ExtMap_to_ExtEnv. unfold adv_ext.
  repeat (apply functional_extensionality; intros).
  rewrite AdvanceMapSound. reflexivity. apply x0.
Qed.

(*
Lemma NoneInvariant : forall (l : list instruction) (env : Env) (ext: ExtMap) (stack1 stack2 : list (option Val)),
    StackEInterp l stack1 env ext false = StackEInterp [] stack2 env ext false -> 
    In None stack1 -> In None stack2.
Proof.
  intros. generalize dependent l. induction l.
  - intros. inversion H. unfold In.

Lemma NoNoneInvariant : forall (l : list instruction) (env : Env) (ext: ExtMap) (stack : list (option Val))
  ,
    StackEInterp l (None::stack) env ext false = None.
Proof.
  intros. 
Qed.
*)
    
Lemma TranlateExpressionStep : forall (e : Exp) (env : Env)  (expis l0 l1 : list instruction)
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
         + admit.
         + admit.
         + admit.
         + admit.
         + admit.
         + admit.
         + admit.
         + admit.
         + admit.
         + admit.
         + rewrite H2. reflexivity.
         + destruct (sequence
                 (map (fun e : Exp => E[| e|] env (ExtMap_to_ExtEnv ext))
                      args)); discriminate.
         + destruct (sequence
                 (map (fun e : Exp => E[| e|] env (ExtMap_to_ExtEnv ext))
                      args)); discriminate.
         + destruct (sequence
                 (map (fun e : Exp => E[| e|] env (ExtMap_to_ExtEnv ext))
                      args)); discriminate.
         + destruct (sequence
                 (map (fun e : Exp => E[| e|] env (ExtMap_to_ExtEnv ext))
                      args)); discriminate.
         + rewrite H2. reflexivity.
         + destruct (sequence
                 (map (fun e : Exp => E[| e|] env (ExtMap_to_ExtEnv ext))
                      args)); discriminate.
         + destruct (sequence
                 (map (fun e : Exp => E[| e|] env (ExtMap_to_ExtEnv ext))
                      args)); discriminate.
         + destruct (sequence
                 (map (fun e : Exp => E[| e|] env (ExtMap_to_ExtEnv ext))
                      args)); discriminate.
         + destruct (sequence
                 (map (fun e : Exp => E[| e|] env (ExtMap_to_ExtEnv ext))
                      args)); discriminate.
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
       - inversion H0. inversion H1. cbn in *. rewrite <- lookupTranslateSound. reflexivity.
       - inversion H0.
         destruct (CompileE e1) eqn:Eq1; try discriminate.
         destruct (CompileE e2) eqn:Eq2; try discriminate.
         cbn in *. clear H0. inversion H2. cbn in *. repeat rewrite <- app_assoc. 
         rewrite IHe2 with
             (expis := (IAccStart2 :: repeat_app (IAccStep :: l) d ++ [IAccEnd]) ++ l1).
         cbn. induction d. 
         + 
       
         
         
Lemma TranlateExpressionStep : forall (e : Exp) (env : Env) (extM : ExtMap) (expis l0 l1 : list instruction)
                                 (stack : list (Env -> ExtMap -> option Val)) (env : Env) (ext: ExtMap) (f: Env -> ExtMap -> option Val),
    expis = l0 ++ l1 -> CompileE e = Some l0 -> (fun env1 ext2 => Esem e env1 (ExtMap_to_ExtEnv ext2)) = f -> 
    StackEInterp (l0 ++ l1) stack env extM false =  StackEInterp l1 (f::stack) env extM false.
Proof. intro. induction e using Exp_ind'; intros.
       - destruct op; inversion H1; try destruct args; try discriminate; try destruct args; try discriminate; try destruct args; try discriminate.

       - inversion H0. cbn. cbn in H1. unfold ExtMap_to_ExtEnv in H1.
         unfold find_default. rewrite H1. reflexivity.
       - inversion H0. cbn. cbn in H1. rewrite <- H1.
         assert (H4: (fun (e : Env' Val) (_ : ExtMap) => StackLookupEnv (translateVarToNat v) e) =
                     (fun (env1 : Env) (_ : ExtMap) => lookupEnv v env1)).
         + apply functional_extensionality. intros. apply functional_extensionality. intros. rewrite lookupTranslateSound. reflexivity.
         + rewrite H4. reflexivity.
       - inversion H0. unfold LApp3 in H3. unfold liftM3 in H3.
         destruct (CompileE e2)  eqn:Eqc2; destruct (CompileE e1) eqn:Eqc1; try (cbn in H1; discriminate).
         cbn in H3. unfold pure in H3. unfold app3 in H3. inversion H3. cbn.
         repeat rewrite <- app_assoc.
         rewrite IHe2 with (expis := (l ++ l2 ++ [IAcc d] ++ l1)) (f :=  (fun (env1 : Env) (ext2 : ExtMap) =>
                                                                            E[| e2 |] env1 (ExtMap_to_ExtEnv ext2))); (try reflexivity).
         rewrite IHe1 with (expis := (l2 ++ [IAcc d] ++ l1)) (f :=  (fun (env1 : Env) (ext2 : ExtMap) =>
                                                                       E[| e1 |] env1 (ExtMap_to_ExtEnv ext2))); (try reflexivity).
         + rewrite <- H1. cbn. assert (H5: (fun (e : Env) (et : ExtMap) =>
      Acc_sem
        (Fsem_stack (fun (env1 : Env) (ext2 : ExtMap) => E[| e1|] env1 (ExtMap_to_ExtEnv ext2)) e
           (adv_map (- Z.of_nat d) et)) d (E[| e2|] e (ExtMap_to_ExtEnv (adv_map (- Z.of_nat d) et)))) = (fun (env1 : Env) (ext2 : ExtMap) =>
      Acc_sem
        (Fsem E[| e1|] env1
           (adv_ext (- Z.of_nat d) (ExtMap_to_ExtEnv ext2))) d
        (E[| e2|] env1 (adv_ext (- Z.of_nat d) (ExtMap_to_ExtEnv ext2))))).
           apply functional_extensionality. intros. apply functional_extensionality. intros.
           * unfold Fsem_stack. unfold Fsem. assert (H6:  (fun (m : nat) (x1 : option Val) =>
     do x' <- x1;
     E[| e1|] (x' :: x)
       (ExtMap_to_ExtEnv (adv_map (Z.of_nat m) (adv_map (- Z.of_nat d) x0)))) = (fun (m : nat) (x1 : option Val) =>
     do x' <- x1;
     E[| e1|] (x' :: x)
      (adv_ext (Z.of_nat m) (adv_ext (- Z.of_nat d) (ExtMap_to_ExtEnv x0))))).
             apply functional_extensionality. intros. rewrite <- AdvanceMap1. rewrite <- AdvanceMap1. reflexivity.
             rewrite H6. rewrite AdvanceMap1. reflexivity.
           * rewrite H5. reflexivity.
         + apply env.
         + apply extM.
         + apply env.
         + apply extM.
Admitted.
 

Theorem TranslateExpressionSound : forall (e : Exp) (env : Env) (extM : ExtMap) (expis : list instruction),
    CompileE e = Some expis ->  Esem e env (ExtMap_to_ExtEnv extM) = vmE expis env extM.
Proof.
  intros. unfold vmE. rewrite (app_nil_end expis).
  rewrite TranlateExpressionStep with (e:=e) (expis:= (expis ++ []))
                                      (f := (fun env1 ext1 => E[| e|] env1 (ExtMap_to_ExtEnv ext1))); (try reflexivity).
  - apply env.
  - apply extM.
  - apply H.
Qed.

Definition vmC (instrs : list CInstruction) (env: Env) (ext: ExtMap) : option TraceM :=
  StackCInterp instrs [] env ext.


Definition vmPartial (instrs : list CInstruction) (env: Env) (ext: ExtMap) : option TraceM :=
  StackCPartial instrs [] env ext.

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

Definition option_traceM_to_Trace (t : option TraceM) (default: Z) : option Trace :=
  liftM2 traceMtoTrace t (Some 0).


(*
Lemma TranlateContractStep : forall (c : Contr) (env : Env) (extM : ExtMap) (instrs l0 l1 : list CInstruction)
                                 (stack : list (Env -> ExtMap -> option TraceM) ) (t: Env -> ExtMap -> option TraceM),
    instrs = l0 ++ l1 -> CompileC c = Some l0 -> (forall env1 ext2, Csem c env1 (ExtMap_to_ExtEnv ext2) =
                                                option_traceM_to_Trace (t env1 ext2) 0) -> 
    StackCInterp (l0 ++ l1) stack env extM = StackCInterp l1 (t::stack) env extM .
Proof.
  intro. induction c; intros.
  - inversion H0. cbn in *. assert (H5: t = (fun (_ : Env) (_ : ExtMap) => Some empty_traceM)).
  
      
Theorem TranslateContractSound : forall (c : Contr) (e : Env) (ext : ExtMap) (instrs : list CInstruction) ,
    CompileC c = Some instrs -> Csem c e (ExtMap_to_ExtEnv ext) = do traceM <- (vmC instrs e ext); Some (traceMtoTrace traceM 0).
Proof.
  intros. unfold vmC. rewrite (app_nil_end instrs). 
*)
