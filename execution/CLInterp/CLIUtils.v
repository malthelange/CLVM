Require Export List.
Require Export Basics.
Require Import Tactics.


Infix "∘" := compose (at level 40, left associativity).

Import ListNotations.

Fixpoint zipWith {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
match xs, ys with
    | (x::xs'), (y::ys') => f x y :: zipWith f xs' ys'
    | _, _ => []
end.

Inductive all {A} (P : A -> Prop) : list A -> Prop :=
| forall_nil : all P nil
| forall_cons {x xs} : P x -> all P xs -> all P (x :: xs).

Lemma all_apply'' {A} (P: A -> Prop) (x: A) (xs: list A) :
  all P (x::xs) -> P x /\ (all P xs).
Proof. intros. inversion H. split.
       - apply H2.
       - apply H3.
Qed.

Hint Constructors all.

Inductive all2 {A B} (R : A -> B -> Prop) : list A -> list B -> Prop :=
| all2_nil : all2 R [] []
| all2_cons {x y xs ys} : R x y -> all2 R xs ys -> all2 R (x::xs) (y::ys).

Hint Constructors all2.

Inductive all3 {A B C} (R : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
| all3_nil : all3 R [] [] []
| all3_cons {x y z xs ys zs} : R x y z -> all3 R xs ys zs -> all3 R (x::xs) (y::ys) (z::zs).

Hint Constructors all3.

Lemma all2_impl {A B} (R1 R2 : A -> B -> Prop) xs ys : 
  (forall x y, R1 x y -> R2 x y) -> all2 R1 xs ys -> all2 R2 xs ys.
Proof.
  intros f l. induction l; auto. 
Qed.


Lemma all2_apply {A B} (P : Type) (p : P) (R : A -> B -> P -> Prop) xs ys : 
  all2 (fun x y => forall (p:P), R x y p) xs ys -> all2 (fun x y => R x y p) xs ys.
Proof.
  intros F. induction F; auto.
Qed.


Lemma all2_and {A B} (R1 R2 : A -> B -> Prop) xs ys : 
  all2 R1 xs ys -> all2 R2 xs ys -> all2 (fun x y => R1 x y /\ R2 x y) xs ys.
Proof.
  intros A1 A2. induction A1; inversion A2; auto.
Qed.


Lemma all2_map {A B} (P : A -> B -> Prop) (f: A -> A) (g : B -> B) xs ys :
  (forall x y, P x y -> P (f x) (g y)) ->
  all2 P xs ys -> all2 P (map f xs) (map g ys).
Proof.
  intros I Z. induction Z;constructor; auto.
Qed.



Lemma all2_map' {A1 A2 B1 B2} P (f : A1 -> B1) (g : A2 -> B2) xs ys : 
  all2 (fun x y => P (f x) (g y)) xs ys -> all2 P (map f xs) (map g ys).
Proof.
  intro L. induction L; constructor;auto.
Qed.
  

Class Partial t := {
  lep : t -> t -> Prop
                  }. 

Infix "⊆" := lep (at level 60).

Definition default {A} (d : A) (x : option A) : A :=
  match x with
    | Some y => y
    | None => d
  end.


Instance none_Partial A : Partial (option A) := {
  lep t1 t2  := forall z , t1 = Some z -> t2 = Some z
  }.


(* Lifts binary functions into [option] types. *)


Definition bind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with
    | None => None
    | Some x' => f x'
  end.

Definition pure {A} : A -> option A := fun x => Some x.


Instance list_Partial {A} : Partial (list (option A)) := {
  lep t1 t2  := all2 lep t1 t2
                                                        }.

Lemma all_apply {A} (P : Type) (p : P) (R : A -> P -> Prop) xs : 
  all (fun x => forall (p:P), R x p) xs -> all (fun x => R x p) xs.
Proof.
  intros F. induction F; auto.
Qed.

Lemma all_map {A B} P (f : A -> B) xs : all (fun x => P (f x)) xs -> all P (map f xs).
Proof.
  intro L. induction L; constructor;auto.
Qed.

Lemma all_map_forall {A B} (P : B -> Prop) (f : A -> B) xs : (forall x, P (f x)) ->  all P (map f xs).
Proof.
  intro L. induction xs; constructor;auto.
Qed.


Lemma all_zip T T' (P : T -> T' -> Prop) l l' f :
  all (fun x => forall t, P x t -> P (f x) t) l -> all2 P l l' -> all2 P (map f l) l'.
Proof.
  generalize dependent l'. induction l; intros.
  + simpl. assumption.
  + simpl. inversion H. inversion H0. subst. constructor. auto. apply IHl; auto.
Qed.

Lemma all_apply' {A} (P Q : Type) (q : Q) (R : A -> P -> Q -> Prop) xs : 
  all (fun x => forall (p:P) (q:Q), R x p q) xs -> all (fun x => forall (p:P), R x p q) xs.
Proof.
  intros F. induction F; auto.
Qed.

Lemma all_mp {A} (P Q : A -> Prop) xs : all P xs -> all (fun x => P x -> Q x) xs -> all Q xs.
Proof.
  intro All. induction All;constructor;inversion H0; auto.
Qed.

Lemma all2_map_all2 {A' A B B'} xs ys P (f : A -> A') (g : B -> B') : 
  all2 (fun x y => P (f x) (g y)) xs ys -> all2 P (map f xs) (map g ys).
Proof. 
  intro Ps. induction Ps;simpl;constructor;auto.
Qed.

Lemma all2_all {A B} P (xs : list A) (ys : list B) : all2 (fun x y => P x) xs ys -> all P xs.
Proof.
  intros T. induction T;constructor;auto.
Qed.


Require Import Reals.

Definition Rleb (x y : R) : bool :=
  match Rle_dec x y with
    | left _ => true
    | right _ => false
  end.

Definition Rltb (s1 s2 : R) : bool :=
  match Rlt_dec s1 s2 with
      | left  _ => true
      | right _ => false
  end.

Open Scope bool.
Definition Reqb (x y : R) : bool := Rleb x y && Rleb y x.

Open Scope R.

Lemma Rleb_iff x y : Rleb x y = true <-> x <= y.
Proof. 
  unfold Rleb. split; intro; destruct (Rle_dec x y) ;auto; discriminate.
Qed.

Lemma Rltb_iff x y : Rltb x y = true <-> x < y.
Proof. 
  unfold Rltb. split; intro; destruct (Rlt_dec x y);auto; discriminate.
Qed.

