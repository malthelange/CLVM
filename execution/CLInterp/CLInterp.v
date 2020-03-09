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

Open Scope Z.
Inductive Val : Set := BVal : bool -> Val | ZVal : Z -> Val.
Parameter BoolObs : Z.
Parameter ZObs : Z.
Parameter TVar : Set.

Set Nonrecursive Elimination Schemes.

Inductive Asset :=
| DKK
| USD.

Definition eqbA (a1 : Asset) (a2 : Asset)  : bool :=
  match a1, a2 with
  | DKK, DKK => true
  | USD, USD => true
  | _,_ => false
  end.
 


Inductive Party :=
| PartyN : nat -> Party.

Program Instance party_serializable : Serializable Party :=
  Derive Serializable Party_rect<PartyN>.


Inductive ObsLabel : Set := LabZ (l: Z) | LabB (l: Z).

(** TODO: REFACTOR Proof of countable and decideable equality from serialization to nat *)

Definition to_sum (t : ObsLabel) :=
  match t with
  | LabZ l => inl l
  | LabB l => inr l
  end.

Definition of_sum (zz : Z + Z) : ObsLabel :=
  match zz with
  | inl l => LabZ l
  | inr r => LabB r
  end.


Lemma of_to_sum t : of_sum (to_sum t) = t.
Proof.
  now destruct t.
Qed.

Lemma to_sum_injective x y :
  to_sum x = to_sum y ->
  x = y.
Proof.
  intros eq.
  assert (of_sum (to_sum x) = of_sum (to_sum y)) by congruence.
  now rewrite !of_to_sum in H.
Qed.

Instance Obs_eqdec : stdpp.base.EqDecision ObsLabel.
Proof.
  intros x y.
  unfold base.Decision.
  destruct (stdpp.base.decide (to_sum x = to_sum y)).
  - left; apply to_sum_injective; auto.
  - right; intros xney.
    subst x.
    congruence.
Defined.

Definition to_nat (p : Party) :=
  match p with
  | PartyN n => n
  end.

Definition of_nat (n : nat) := PartyN n.

Lemma of_to_nat p : of_nat (to_nat p) = p.
Proof.
  now destruct p.
Qed.



Lemma to_int_injective x y  : to_nat x = to_nat y ->
                              x = y.
Proof. intros.
       assert (of_nat (to_nat x) = of_nat (to_nat y)) by congruence. now rewrite !of_to_nat in H0.
Qed.

Definition to_natA (a : Asset) :=
  match a with
  | DKK => 0%nat
  | USD => 1%nat
  end.

Definition of_natA (n : nat) :=
  match n with
  | 0%nat => DKK
  | _ => USD
  end.

Lemma of_to_natA a : of_natA (to_natA a) = a.
Proof.
  now destruct a.
Qed.

Lemma to_natA_injective x y  : to_natA x = to_natA y ->
                              x = y.
Proof. intros.
       assert (of_natA (to_natA x) = of_natA (to_natA y)) by congruence. now rewrite !of_to_natA in H0.
Qed.

Instance Asset_eqdec : stdpp.base.EqDecision Asset.
Proof.
  intros x y.
  unfold base.Decision.
  destruct (stdpp.base.decide (to_natA x = to_natA y)).
  - left; apply to_natA_injective; auto.
  - right; intros xney.
    subst x. congruence.
Defined.
Instance Party_eqdec : stdpp.base.EqDecision Party.
Proof.
  intros x y.
  unfold base.Decision.
  destruct (stdpp.base.decide (to_nat x = to_nat y)).
  - left; apply to_int_injective; auto.
  - right; intros xney.
    subst x. congruence.
Defined.

Instance Obs_countable : countable.Countable ObsLabel.
Proof.
  refine {| countable.encode t := countable.encode (to_sum t);
                     countable.decode p := do zz <- countable.decode p;
                                           Some (of_sum zz) |}.
  intros x.
  rewrite countable.decode_encode.
  cbn.
  now rewrite of_to_sum.
Defined.

Instance Party_countable : countable.Countable Party.
Proof.
  refine {| countable.encode t := countable.encode (to_nat t);
                     countable.decode p := do zz <- countable.decode p;
                                              Some (of_nat zz) |}.
  intros x. rewrite countable.decode_encode. cbn. now rewrite of_to_nat.
Defined.


Instance Asset_countable : countable.Countable Asset.
Proof.
  refine {| countable.encode t := countable.encode (to_natA t);
                     countable.decode p := do zz <- countable.decode p;
                                              Some (of_natA zz) |}.
  intros x. rewrite countable.decode_encode. cbn. now rewrite of_to_natA.
Defined.


Program Instance Obs_serializable : Serializable ObsLabel :=
      Derive Serializable ObsLabel_rect<LabZ, LabB>.

  
Definition OLEq (l1: ObsLabel) (l2 : ObsLabel) :=
  match l1, l2 with
  | (LabZ z1) , (LabZ z2) => z1 =? z2
  | (LabB z1) , (LabB z2) => z1 =? z2
  | _ , _ => false 
  end.

Inductive Var : Set := V1 | VS (v:Var).


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


Definition Env' A := list A.

Fixpoint lookupEnv {A} (v : Var) (env : Env' A) : option A :=
  match v, env with
    | V1, x::_ => Some x
    | VS v, _::xs => lookupEnv v xs
    | _,_ => None
  end.

Fixpoint StackLookupEnv {A} (n : nat) (env : Env' A) : option A :=
  match n, env with
    | O, x::_ => Some x
    | S n', _::xs => StackLookupEnv n' xs
    | _,_ => None
  end.

Fixpoint translateVarToNat (v : Var) :=
  match v with
  | V1 => O
  | VS v' => S (translateVarToNat v')
  end.

Lemma lookupTranslateSound : forall (A: Type) (env : (Env' A)) (v : Var),  lookupEnv v env = StackLookupEnv (translateVarToNat v) env. 
Proof.
  intros. generalize dependent v. induction env.
  - intros. destruct v; reflexivity.
  - intros v. destruct v.
    + reflexivity.
    + cbn. apply IHenv.
Qed.
  
       
Definition Env := Env' Val.

Definition ExtEnv' A := ObsLabel -> Z -> A.

Definition adv_ext {A} (d : Z) (e : ExtEnv' A) : ExtEnv' A
  := fun l x => e l (d + x)%Z.


Definition ExtEnv := ExtEnv' Val.

Definition ExtMap := FMap (ObsLabel * Z) Val.
Program Instance Val_Serializable : Serializable Val :=
  Derive Serializable Val_rect<BVal, ZVal>.
Instance ExtMapSerializable : Serializable ExtMap := _.

Definition ExtMap_to_ExtEnv (extM : ExtMap) : ExtEnv := fun l i => match FMap.find (l,i) extM with
                                                                | None => ZVal 0
                                                                | Some v => v
                                                                end.

Definition empt : FMap (ObsLabel * Z) Val := FMap.empty.
Definition updated : ExtMap := FMap.add ((LabZ 1), 1) (ZVal 20) empt.

Fixpoint adv_map_aux (l : list (ObsLabel * Z * Val)) (d : Z) :=
  match l with
  | [] => []
  | (l , z , v)::tl => (l, z - d, v)::(adv_map_aux tl d)
  end.
               

Definition adv_map (d : Z) (e : ExtMap) : ExtMap
  := FMap.of_list (adv_map_aux (FMap.elements e) d).
(**
   Compute FMap.find (LabZ 1, 1) updated. 
   Compute FMap.find (LabZ 1, 1) (adv_map 2 updated). 
   Compute FMap.find (LabZ 1, 3) (adv_map 2 updated). 
*)


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

Definition Trans := Party -> Party -> Asset -> Z.
Definition TransM := FMap Party (FMap Party (FMap Asset Z)).


Instance asset_serializable : Serializable Asset :=
  Derive Serializable Asset_rect<DKK, USD>.

Instance TransSerial : Serializable TransM := _.

Definition empty_trans : Trans := fun p1 p2 c => 0.
Definition empty_transM : TransM := FMap.empty.
(** TODO: Make party a part of the Eqb class to simplify *)
Definition singleton_trans (p1 p2 : Party) (a : Asset) (z: Z) : Trans :=
  match p1, p2 with
  | PartyN pn1, PartyN pn2 => if (pn1 =? pn2)%nat then empty_trans else
                               fun p1' p2' a' => match p1', p2' with
                                              | PartyN pn1', PartyN pn2' =>
                                                if ((pn1 =? pn1')%nat && ((pn2 =? pn2')%nat && (eqbA a a'))%bool)%bool
                                                then z
                                                else if andb (pn1 =? pn2')%nat (andb (pn2 =? pn1')%nat (eqbA a a'))
                                                     then -z
                                                     else 0
                                              end
  end.


Definition singleton_transM (p1 p2 : Party) (a : Asset) (z: Z) : TransM :=
  match p1, p2 with
  | PartyN pn1, PartyN pn2 => if (pn1 =? pn2)%nat then FMap.empty else
                               let azp : FMap Asset Z := FMap.add a z FMap.empty in
                               let azm : FMap Asset Z := FMap.add a (-z) FMap.empty in
                               let p2azp : FMap Party (FMap Asset Z) := FMap.add p2 azp FMap.empty  in
                               let p1azm : FMap Party (FMap Asset Z) := FMap.add p1 azm FMap.empty  in
                               let p1p2azp : TransM := FMap.add p1 p2azp FMap.empty in
                               FMap.add p2 p1azm (p1p2azp)
  end.


Definition lookup_transM (p1 p2 : Party) (a : Asset) (t : TransM) :=
  do l1 <- FMap.find p1 t ;
  do l2 <- FMap.find p2 l1 ;
  FMap.find a l2.

Definition add_trans : Trans -> Trans -> Trans := fun t1 t2 p1 p2 c => (t1 p1 p2 c + t2 p1 p2 c).
Definition add_transM : TransM -> TransM -> TransM :=
  FMap.union_with (fun paz1 paz2 => Some (FMap.union_with (fun az1 az2 => Some (FMap.union_with (fun z1 z2 => Some (z1 + z2)) az1 az2) ) paz1 paz2)).

(** TODO 
    Refactor 
 *)

Fixpoint scale_aux3 (s : Z) (l : list (Asset * Z)) : FMap Asset Z :=
  match l with
  | [] => FMap.empty
  | (a, z)::tl => FMap.add a (z * s) (scale_aux3 s tl)
  end.

Fixpoint scale_aux2 (s: Z) (l : list (Party * (FMap Asset Z))) : FMap Party (FMap Asset Z) :=
  match l with
  | [] => FMap.empty
  | (p2, az)::tl => FMap.add p2 (scale_aux3 s (FMap.elements az)) (scale_aux2 s tl)
  end.

Fixpoint scale_aux1 (s: Z) (l : list (Party * (FMap Party (FMap Asset Z)))) : TransM :=
     match l with
     | [] => FMap.empty
     | (p1, paz)::tl => FMap.add p1 (scale_aux2 s (FMap.elements paz)) (scale_aux1 s tl)
     end.

Fixpoint scale_transM (s : Z) (t : TransM) :=
  scale_aux1 s (FMap.elements t).
(** Test Code 
Definition p1 := PartyN 1.
Definition p2 := PartyN 2.
Definition p3 := PartyN 3.

Definition t1 := singleton_transM p1 p2 DKK 1.
Definition t2 := singleton_transM p2 p3 DKK 2.
Definition u12 := add_transM t1 t2.
Compute lookup_transM p1 p2 DKK (scale_transM 3 u12).
*)

Definition scale_trans : Z -> Trans -> Trans := fun s t p1 p2 c => (t p1 p2 c * s).

Definition Trace := nat -> Trans.

Definition TraceM := FMap nat TransM.
Instance TraceSerial : Serializable TraceM := _.

(* The following are combinators to contruct traces. *)

Definition const_trace (t : Trans) : Trace := fun x => t.
Definition empty_trace : Trace := const_trace empty_trans.

Definition empty_traceM : TraceM := FMap.empty.

Definition singleton_trace (t : Trans) : Trace
  := fun x => match x with 
                | O => t
                | _ => empty_trans
           end.

Definition singleton_traceM (t: TransM) : TraceM := FMap.add 0%nat t empty_traceM.

Definition scale_trace (s : Z) (t : Trace) : Trace
  := fun x => scale_trans s  (t x).

Definition scale_traceM (s : Z) (t: TraceM) : TraceM :=
FMap.of_list (List.map (fun e : nat * TransM => match e with | (n,t1) => (n, (scale_transM s t1)) end) (FMap.elements t)).

Definition delay_trace (d : nat) (t : Trace) : Trace :=
  fun x => if (leb d x)
           then t (x - d)%nat
        else empty_trans.

Definition delay_traceM (d : nat) (t : TraceM) : TraceM :=
  FMap.of_list
    (List.map (fun e : nat * TransM => match e with
                                  | (n,trans) =>
                                    ((n + d)%nat, trans) end)
              (FMap.elements t)).

Definition add_trace (t1 t2 : Trace) : Trace 
  := fun x => add_trans (t1 x) (t2 x).

Definition add_traceM (t1 t2 : TraceM) : TraceM :=
  FMap.union_with (fun trans1 trans2 => Some (add_transM trans1 trans2)) t1 t2.

Definition toZ (v : Val) : option Z := 
  match v with
  | ZVal z => Some z
  | _ => None
  end.

  
Reserved Notation "'C[|' e '|]'" (at level 9).
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

  Definition lit10 := OpE (ZLit 10) [].
  Definition lit3 := OpE (ZLit 3) [].
  Definition lit4 := OpE (ZLit 4) [].
  Definition obs1 := Obs (LabZ 1) 0.
  Definition obs2 := Obs (LabZ 2) 0.
  Definition obs_bool := Obs (LabB 0) 4.
  Definition p1 := PartyN 1.
  Definition p2 := PartyN 2.

  Definition exmp1 := (OpE Sub [lit10; (OpE Add [lit4; lit3])]).
  Definition exmp2 := OpE Leq [lit4; exmp1].
  Definition exmp3 := OpE Cond [exmp2; lit4; exmp1].

  Compute CompileRunE exmp3.
  Compute Esem exmp3 [] def_ext.

  
  Definition update_ext (l1 : ObsLabel) (i1 : Z) (vn : Val)  (e : ExtEnv) := (fun l i => if ((OLEq l l1) && (i =? i1))%bool then vn else e l i).
 
  Notation "'ifc' e 'within' n 'then' c1 'else' c2" := (If e n c1 c2) (at level 100, e at next level, right associativity).
  Notation "'obsB' '(' z1 ';' z2 ')'" := (Obs (LabB z1) z2) (at level 100, right associativity).
  Notation "'lbB' '(' z1 ')'" := (LabB z1) .
  Notation "'Ø'" := Zero.
  Notation "e 'X' c" := (Scale e c) (at level 100, right associativity).
  Notation "c '(' p1 '--->' p2 ')'" := (Transfer p1 p2 c)(at level 100, right associativity).
  Notation "d '^|' c" := (Translate d c)(at level 100, right associativity).
  Definition ext_exmp1 := update_ext (LabZ 1) 4 (ZVal 20) (update_ext (LabB 0) 4 (BVal true) (update_ext (LabZ 2) 1 (ZVal (-4)) (update_ext (LabZ 1) 0 (ZVal 1) (update_ext  (LabZ 1) 1 (ZVal 2) def_ext )))).

 Definition extm_exmp1 : FMap (ObsLabel * Z) Val := FMap.add ((LabZ 1),4) (ZVal 20) (FMap.add ((LabB 0),4) (BVal true) (FMap.add ((LabZ 2),1) (ZVal (-4)) (FMap.add ((LabZ 1),0) (ZVal 1) (FMap.add ((LabZ 1),1) (ZVal 2) def_extM)))).

  Compute ext_exmp1 (LabB 0) 4.
Definition c_exmp1 := (Scale obs1 (Transfer (PartyN 1) (PartyN 2) DKK)).
Definition c_exmp2 := (Translate 1 (Scale obs2 (Transfer (PartyN 1) (PartyN 2) DKK))).
Definition c_exmp3 := (Both c_exmp1 c_exmp2).
Definition c_exmp4 := Translate 1 (Both ((Scale obs1 (Transfer (PartyN 1) (PartyN 2) DKK))) (Scale obs2 (Transfer (PartyN 1) (PartyN 2) DKK))).

Definition std_option := ifc obs_bool within 30 then c_exmp1 else Ø.
Definition over_price := OpE Leq [obs1 ; OpE Mult [VarE V1; (OpE (ZLit 2) [])]].
Definition let_option := Let obs1 (ifc over_price within 30 then Ø else c_exmp1).


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

Compute lookupTrace (Csem c_exmp1 [] (ExtMap_to_ExtEnv extm_exmp1)) 0 p1 p2 DKK.
Compute lookupTraceM (CompileRunC c_exmp1 [] extm_exmp1) 0 p1 p2 DKK.


(** ERROR HERE find_default returns Default when it is not supposed to *)

Lemma c1 : (Csem c_exmp1 [] (ExtMap_to_ExtEnv extm_exmp1)) =  (CompileRunC c_exmp1 [] extm_exmp1) .
Proof. reflexivity. Qed.

  Lemma c2 : (Csem c_exmp2 [] ext_exmp1) =  (CompileRunC c_exmp2 [] extm_exmp1).
    Proof. reflexivity. Qed.

 Lemma c3 : (Csem c_exmp3 [] ext_exmp1) = (CompileRunC c_exmp3 [] extm_exmp1).
Proof. reflexivity. Qed.
Lemma c4 : (Csem c_exmp4 [] ext_exmp1) = (CompileRunC c_exmp4 [] extm_exmp1) .
Proof. reflexivity. Qed.
Lemma c5 : (Csem std_option [] ext_exmp1) = (CompileRunC std_option [] extm_exmp1).
Proof. reflexivity. Qed.

Compute lookupTrace (Csem std_option [] ext_exmp1) 1 p1 p2 DKK.
Compute lookupTrace (Csem let_option [] ext_exmp1) .

  Lemma test1 : (CompileRunE exmp1) = Esem exmp1 [] def_ext.
  Proof. reflexivity. Qed.

  Lemma test2 : (CompileRunE exmp2) = Esem exmp2 [] def_ext.
  Proof. reflexivity. Qed.

  Lemma test3 : (CompileRunE exmp3) = Esem exmp3 [] def_ext.
  Proof. reflexivity. Qed.

  

  Section Interp.
    Context `{Base : ChainBase}.


    Record Setup :=
      build_setup {
          setup_contract : list CInstruction;
        }.

    Record State :=
      build_state {
          contract : list CInstruction;
          result : option Trace;
        }.

    Inductive Msg :=
    | update : ExtEnv -> Msg.                          

    Program Instance Op_serializable : Serializable Op :=
      Derive Serializable Op_rect <Add, Sub, Mult, Div, And, Or, Less, Leq, Equal, Not, Neg, BLit, ZLit, Cond>.
    Program Instance instruction_serializable : Serializable instruction :=
      Derive Serializable instruction_rect<IPushZ, IPushB, IObs, IOp, IAcc, IVar>.
    
    Program Instance Env_Serializable : Serializable Env := _.

    Instance CInstruction_serializable : Serializable CInstruction := 
      Derive Serializable CInstruction_rect< CIZero, CITransfer, CIScale, CIBoth, CITranslate, CILet, CIIf>.

    Instance SetupSerial : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.


    Instance StateSerial : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Definition m : ExtEnv := fun a b => BVal false.

    Check to_list m.
    
    Instance ExtSerial : Serializable ExtEnv :=
      Derive Serializable ExtEnv_rect<update>.
    Instance MsgSerial : Serializable Msg :=
      Derive Serializable Msg_rect<update>.
    
   
