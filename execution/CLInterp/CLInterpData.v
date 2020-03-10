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



Inductive ObsLabel : Set := LabZ (l: Z) | LabB (l: Z).


Set Nonrecursive Elimination Schemes.


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

Definition Env' A := list A.


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



Definition OLEq (l1: ObsLabel) (l2 : ObsLabel) :=
  match l1, l2 with
  | (LabZ z1) , (LabZ z2) => z1 =? z2
  | (LabB z1) , (LabB z2) => z1 =? z2
  | _ , _ => false 
  end.


Definition Env := Env' Val.

Definition ExtEnv' A := ObsLabel -> Z -> A.

Definition adv_ext {A} (d : Z) (e : ExtEnv' A) : ExtEnv' A
  := fun l x => e l (d + x)%Z.


Definition ExtEnv := ExtEnv' Val.

Definition ExtMap := FMap (ObsLabel * Z) Val.
