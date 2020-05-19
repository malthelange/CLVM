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
Require Import Sorting.Permutation.
Require Import Coq.Init.Datatypes.
Require Import Coq.micromega.Lia.


Require Import Serializable.
From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.
Require Import Coq.Logic.Classical_Prop.

Open Scope Z.
(** Basic datatypes needed for CL and CLVM *)
Inductive Val : Set := BVal : bool -> Val | ZVal : Z -> Val.
Parameter BoolObs : Z.
Parameter ZObs : Z.
Parameter TVar : Set.

Definition Asset := nat.

Definition Party := nat.

Inductive ObsLabel : Set := LabZ (l: Z) | LabB (l: Z).

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

(** TODO: 
Proof of decideable equality and countability datatypes, needed for serialization
REFACTOR Proof of countable and decideable equality from serialization to nat *)

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

(*
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
*)

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
(*
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
*)

Definition OLEq (l1: ObsLabel) (l2 : ObsLabel) :=
  match l1, l2 with
  | (LabZ z1) , (LabZ z2) => z1 =? z2
  | (LabB z1) , (LabB z2) => z1 =? z2
  | _ , _ => false 
  end.


(** Definition of environments for CL and CLVM *)
Inductive Var : Set := V1 | VS (v:Var).

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


Definition Env := Env' Val.
Definition EnvOp := Env' (option Val).

Definition ExtEnv' A := ObsLabel -> Z -> A.

Definition adv_ext {A} (d : Z) (e : ExtEnv' A) : ExtEnv' A
  := fun l x => e l (d + x)%Z.


Definition ExtEnv := ExtEnv' Val.

Definition ExtMap := FMap (ObsLabel * Z) Val.

Definition ExtMap_to_ExtEnv (extM : ExtMap) : ExtEnv := fun l i => match FMap.find (l,i) extM with
                                                                   | None => ZVal 0
                                                                   | Some v => v
                                                                end.

(** Interfaces for advancing environments *)

Definition empt : FMap (ObsLabel * Z) Val := FMap.empty.
Definition TransM := FMap (Party * Party * Asset) Z.
Definition TraceM := FMap nat TransM.

Definition adv_elem (d : Z) ( x : ObsLabel * Z * Val) : ObsLabel * Z * Val
  := base.prod_map (base.prod_map id (fun x => x - d)) id x.

Definition delay_elem (d : nat) ( x : nat * TransM) : nat * TransM
  := base.prod_map (fun n => (n + d)%nat) id x.

Definition scale_trans_elem (z : Z) ( x : Party * Party * Asset * Z) : (Party * Party * Asset * Z)
  := base.prod_map id (fun z' : Z => z * z' ) x.

Definition adv_list (d : Z) (xs : list (ObsLabel * Z * Val))
  : list (ObsLabel * Z * Val)
  := map (adv_elem d) xs.

Definition delay_list (d : nat) (xs : list (nat * TransM))
  : list (nat * TransM)
  := map (delay_elem d) xs.

Definition scale_trans_list (z : Z) (xs : list (Party * Party * Asset * Z))
  : list (Party * Party * Asset * Z)
  := map (scale_trans_elem z) xs.

Definition adv_map (d : Z) (e : ExtMap) : ExtMap
  := FMap.of_list (adv_list d (FMap.elements e)).

Definition delay_traceM (d : nat) (e : TraceM) : TraceM
  := FMap.of_list (delay_list d (FMap.elements e)).

Definition scale_transM (z : Z) (e : TransM) : TransM
  := FMap.of_list (scale_trans_list z (FMap.elements e)).

Lemma prod_map_compose_fst { A A' B B' } (f : A -> A') (g : B -> B'):
  compose fst  (base.prod_map f g) = compose f  fst.
 unfold compose. apply functional_extensionality. intros. unfold base.prod_map. cbn. reflexivity.
Qed.

Lemma prod_map_inj { A A' B B' } (f : A -> A') (g : B -> B') :
  FinFun.Injective f ->
  FinFun.Injective g ->
  FinFun.Injective (base.prod_map f g).
Proof.
  unfold FinFun.Injective. intros. unfold base.prod_map in H1.
  inversion H1. apply injective_projections. apply H. apply H3.
  apply H0. apply H4.
Qed.

Definition exmp : ExtMap := FMap.empty.
(*
Lemma ArithAuth : forall  (a b c : Z),
    a <> 0 -> a * b = a * c -> b = c.
Proof. intro. induction a using Z.peano_ind; intros.
       - lia.
       - repeat rewrite Z.mul_succ_l in H0.
 *)

Lemma scale_trans_list_sound l k1 k2 k3 v z :
  In ((k1, k2, k3), v) l ->
  In ((k1, k2, k3), z * v) (scale_trans_list z l).
Proof. intro.
  induction l; auto; intros.
  - inversion H.
    + destruct a. destruct p. destruct p. cbn.
      left. inversion H0. unfold scale_trans_elem. unfold base.prod_map. cbn. reflexivity.
    + right. apply IHl in H0. apply H0.
Qed.

Lemma scale_trans_list_aux l k1 k2 k3 z v:
  In ((k1, k2, k3), v) (scale_trans_list z l) ->
  (exists v', In ((k1, k2, k3), v') l).
Proof.
  intro. induction l. cbn in H.
  - contradiction.
  - inversion H. destruct a. destruct p. destruct p. unfold scale_trans_elem in H0.
    unfold base.prod_map in H0. cbn in H0. inversion H0.
    + exists (z0). left. reflexivity.
    + apply IHl in H0. destruct H0. exists x. right. apply H0.
Qed.
  

Lemma scale_trans_list_none l k1 k2 k3 z :
  (forall v, ~ In ((k1, k2, k3), v) l) ->
  (forall v, ~ In ((k1, k2, k3), v) (scale_trans_list z l)).
Proof. intros. intro. 
       apply scale_trans_list_aux in H0. destruct H0.
       destruct H with (v:=x).
       apply H0.
Qed.

Lemma map_adv_list_sound l k1 k2 v d :
  In ((k1, k2), v) (adv_list d l) <->
  In ((k1, k2 + d), v) l.
Proof.
  induction l; auto.
  split; intros. 
  - inversion H.
    + inversion H0. destruct a. destruct p. cbn. left. assert (H5: z = z - d + d) by lia.
      rewrite <- H5. reflexivity.
    + right. apply IHl. apply H0.
  - inversion H.
    + destruct a. destruct p. cbn. left. unfold adv_elem.
      unfold id. unfold base.prod_map. cbn. inversion H0.
      replace (k2 + d - d) with k2 by lia. reflexivity.
    + apply IHl in H0. right. apply H0.
Qed.

Lemma delay_trace_list_sound l k1 v d :
  In ((k1 + d)%nat, v) (delay_list d l) <->
  In (k1, v) l.
Proof.
  induction l; auto.
  split; intros. 
  - inversion H.
    + inversion H0. destruct a. cbn in *. left. assert (H5: n = k1) by lia.
      rewrite <- H5. reflexivity.
    + right. apply IHl. apply H0. 
  - inversion H. 
    + destruct a. cbn in *. left. unfold delay_elem.
      unfold id. unfold base.prod_map. cbn in *. inversion H0.
      reflexivity.
    + apply IHl in H0. right. apply H0.
Qed.

Lemma delay_trace_list_none l k1 v d :
    (d > k1)%nat ->
    ~ In (k1, v) (delay_list d l).
Proof.
  intros. induction l.
  - cbn. auto.
  - intro. destruct H0. unfold delay_elem in H0. unfold base.prod_map in H0.
    destruct a. cbn in H0. inversion H0. lia. auto.
Qed.

Lemma map_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (compose g f) l.
Proof.
  intros. induction l.
  reflexivity.
  cbn. rewrite IHl. reflexivity.
Qed.

Lemma perm_scale_list (m : FMap (Party * Party * Asset) Z) (d : Z)
      (l : list (Party * Party * Asset * Z)):
  NoDup (map fst l) ->
  Permutation (FMap.elements (FMap.of_list (scale_trans_list d l))) (scale_trans_list d l).
Proof.
  intros. apply FMap.elements_of_list.  unfold scale_trans_list.
  rewrite map_map_compose. unfold scale_trans_elem. rewrite prod_map_compose_fst.
  rewrite <- map_map_compose. apply FinFun.Injective_map_NoDup. unfold FinFun.Injective.
  intros. auto. apply H.
Qed.

Lemma perm_adv_list (m : FMap (ObsLabel * Z) Val) (d : Z)
      (l : list (ObsLabel * Z * Val)):
  NoDup (map fst l) ->
  Permutation (FMap.elements (FMap.of_list (adv_list d l))) (adv_list d l).
Proof. 
  intros. apply FMap.elements_of_list. unfold adv_list. rewrite map_map_compose.
  unfold adv_elem. rewrite prod_map_compose_fst. rewrite <- map_map_compose.
  apply FinFun.Injective_map_NoDup. unfold FinFun.Injective.
  intros. apply prod_map_inj in H0. apply H0. unfold FinFun.Injective. intros. cbn in H1.
  apply H1.  unfold FinFun.Injective. intros. lia. apply H.
Qed.

Lemma perm_delay_list (m : FMap nat TransM) (d : nat)
      (l : list (nat * TransM)):
  NoDup (map fst l) ->
  Permutation (FMap.elements (FMap.of_list (delay_list d l))) (delay_list d l).
Proof. 
  intros. apply FMap.elements_of_list. unfold delay_list. rewrite map_map_compose.
  unfold delay_elem. rewrite prod_map_compose_fst. rewrite <- map_map_compose.
  apply FinFun.Injective_map_NoDup. unfold FinFun.Injective.
  intros. lia. apply H. 
Qed.


Lemma DelayTraceMSound : forall (trace: TraceM) (d i: nat),
FMap.find i trace = FMap.find (i + d)%nat (delay_traceM d trace).
Proof. intros. destruct (FMap.find _) eqn:find.
  - apply FMap.In_elements in find.
    symmetry. 
    apply FMap.In_elements.
    unfold delay_traceM.
    assert (H: Permutation (FMap.elements (FMap.of_list (delay_list d (FMap.elements trace))))
                           (delay_list d (FMap.elements trace))).
    apply perm_delay_list. apply trace. apply FMap.NoDup_keys.
    apply Permutation_in with (l := (delay_list d (FMap.elements trace))). apply Permutation_sym in H.
    apply H.
    apply delay_trace_list_sound. apply find.
  - symmetry. rewrite <- FMap.not_In_elements with (k:= i) (m:=trace )in find.
    apply FMap.not_In_elements.
    intros v isin. specialize (find v).
    unfold delay_traceM in isin.
    assert (H: Permutation (FMap.elements (FMap.of_list (delay_list d (FMap.elements trace))))
                           (delay_list d (FMap.elements trace))).
    apply perm_delay_list. apply trace. apply FMap.NoDup_keys.
    assert (H1:  In ((i + d)%nat, v)  (delay_list d (FMap.elements trace))).
    apply Permutation_in
      with (l := (FMap.elements (FMap.of_list (delay_list d (FMap.elements trace))))).
    apply H. apply isin. apply delay_trace_list_sound in H1. contradiction.
Qed.

Lemma DelayTraceMNone : forall (trace : TraceM) (d i : nat),
    (d > i)%nat ->
    FMap.find i (delay_traceM d trace) = None.
  intros. apply FMap.not_In_elements. intro. unfold delay_traceM.
  assert (H1: Permutation (FMap.elements (FMap.of_list (delay_list d (FMap.elements trace))))
                          (delay_list d (FMap.elements trace))).
  apply perm_delay_list. apply trace. apply FMap.NoDup_keys.
  intro. apply Permutation_in with (l':= (delay_list d (FMap.elements trace))) in H0.
  assert (~In (i, v) (delay_list d (FMap.elements trace))).
  apply delay_trace_list_none. apply H. auto.
  apply H1.
Qed.

Lemma AdvanceMapSound : forall (ext: ExtMap) (d i: Z) (l : ObsLabel),
FMap.find (l,d + i) ext = FMap.find (l,i) (adv_map d ext).
Proof. intros. destruct (FMap.find _ _) eqn:find.
  - apply FMap.In_elements in find.
    symmetry.
    apply FMap.In_elements.
    rewrite Z.add_comm in find.
    unfold adv_map.
    assert (H: Permutation (FMap.elements (FMap.of_list (adv_list d (FMap.elements ext))))
                           (adv_list d (FMap.elements ext))).
    apply perm_adv_list. apply ext. apply FMap.NoDup_keys.
    apply Permutation_in with (l := (adv_list d (FMap.elements ext))). apply Permutation_sym in H.
    apply H.
    apply map_adv_list_sound. apply find.
   - symmetry.
    rewrite <- FMap.not_In_elements with (k:= (l, d + i)) (m := ext) in find.
    apply FMap.not_In_elements.
    intros v isin.
    specialize (find v).
    rewrite Z.add_comm in find.
    unfold adv_map in isin.
        assert (H: Permutation (FMap.elements (FMap.of_list (adv_list d (FMap.elements ext))))
                           (adv_list d (FMap.elements ext))).
        apply perm_adv_list. apply ext. apply FMap.NoDup_keys.
        assert (H1:  In (l, i, v) (adv_list d (FMap.elements ext))).
        apply Permutation_in
          with (l := (FMap.elements (FMap.of_list (adv_list d (FMap.elements ext))))).
        apply H. apply isin. apply map_adv_list_sound in H1. contradiction.
Qed.


(** Definition of transactions and traces for CL and CLVM along with combinators *)
Definition Trans := Party -> Party -> Asset -> Z.

Definition empty_trans : Trans := fun p1 p2 c => 0.
Definition empty_transM : TransM := FMap.empty.
(** TODO: Make party a part of the Eqb class to simplify *)
Definition singleton_trans (p1 p2 : Party) (a : Asset) (z: Z) : Trans :=
  if (p1 =? p2)%nat then empty_trans else
    fun p1' p2' a' =>
      if ((p1 =? p1')%nat && ((p2 =? p2')%nat && ( a =? a')%nat)%bool)%bool
      then z
      else if andb (p1 =? p2')%nat (andb (p2 =? p1')%nat (a =? a')%nat)
           then -z
           else 0.

Definition singleton_transM (p1 p2 : Party) (a : Asset) (z: Z) : TransM :=
   if (p1 =? p2)%nat then FMap.empty else
     FMap.add (p2, p1, a) (-z) (FMap.add (p1, p2, a) z (FMap.empty)).


Definition lookup_transM (p1 p2 : Party) (a : Asset) (t : TransM) :=
  FMap.find (p1, p2, a) t.

Definition add_trans : Trans -> Trans -> Trans := fun t1 t2 p1 p2 c => (t1 p1 p2 c + t2 p1 p2 c).
Definition add_transM  (t1 t2 : TransM) : TransM :=
  FMap.union_with (fun z1 z2 => Some (z1 + z2)) t1 t2.

Fixpoint scale_transM (s : Z) (t : TransM) :=
  let keys := FMap.keys t in
  List.fold_right (fun (k: (Party * Party * Asset)) (tacc: TransM)   => FMap.alter (fun z => s * z) k tacc) t keys.

Definition scale_trans : Z -> Trans -> Trans := fun s t p1 p2 c => (t p1 p2 c * s).

Definition Trace := nat -> Trans.


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

Fixpoint scale_traceM (s : Z) (t : TraceM) :=
  let keys := FMap.keys t in
  List.fold_right (fun  (k: nat) (tacc: TraceM) => FMap.alter (fun trans => scale_transM s trans) k tacc) t keys.

Definition delay_trace (d : nat) (t : Trace) : Trace :=
  fun x => if (leb d x)
           then t (x - d)%nat
           else empty_trans.

Definition add_trace (t1 t2 : Trace) : Trace 
  := fun x => add_trans (t1 x) (t2 x).

Definition add_traceM (t1 t2 : TraceM) : TraceM :=
  FMap.union_with (fun trans1 trans2 => Some (add_transM trans1 trans2)) t1 t2.

Lemma lookupTranslateSound : forall (A: Type) (env : (Env' A)) (v : Var),  lookupEnv v env = StackLookupEnv (translateVarToNat v) env. 
Proof.
  intros. generalize dependent v. induction env.
  - intros. destruct v; reflexivity.
  - intros v. destruct v.
    + reflexivity.
    + cbn. apply IHenv.
Qed.
