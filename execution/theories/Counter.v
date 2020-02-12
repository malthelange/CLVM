From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From Coq Require Import Psatz.
Require Import Automation.
Require Import Blockchain.
Require Import Extras.
Require Import Monads.
Require Import Serializable.
From RecordUpdate Require Import RecordUpdate.

Import ListNotations.
Import RecordSetNotations.

Section Counter.
  Context `{Base : ChainBase}.
  Set Nonrecursive Elimination Schemes.
  Record Setup :=
    build_setup {
        setup_initial : nat;
    }.

  Record State :=
  build_state {
      count : nat;
    }.

  Inductive Msg :=
  | tick.

  Global Instance State_settable : Settable _ :=
    settable! build_state <count>.

  Global Instance Setup_serializable : Serializable Setup :=
    Derive Serializable Setup_rect<build_setup>.

  Global Instance State_serializable : Serializable State :=
    Derive Serializable State_rect<build_state>.

  Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<tick>.

  Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup)
    : option State :=
    let setup_init := setup_initial setup in
    if 1 <=? setup_init then Some (build_state setup_init) else None.

  Definition receive
             (chain : Chain) (ctx : ContractCallContext)
             (state : State) (msg : option Msg)
    : option (State * list ActionBody) :=
    match msg with
    | None => Some (state, [])
    | Some tick => Some (state<|count := (count state) +1 |>, [])
    end.

  Program Definition contract : Contract Setup Msg State :=
    build_contract init _ receive _.

  Section theories.
    Lemma ge_1_counter bstate caddr:
      reachable bstate ->
      env_contracts bstate caddr = Some (Counter.contract : WeakContract) ->
      exists cstate,
      contract_state bstate caddr = Some cstate ->
      1 <=? (count cstate) = true.
    Proof. intros. contract_induction; intros; cbn in *; auto.
           - destruct result. unfold count. unfold init in init_some. destruct count0.
             destruct setup_initial; discriminate init_some. reflexivity.
           - unfold receive in receive_some. destruct msg. destruct m;
             inversion receive_some. cbn in *. destruct prev_state. unfold count.
             destruct count0; cbn; try reflexivity.
             inversion receive_some. rewrite <- H1. apply IH. rewrite <- H1 in H. apply H.
           - unfold receive in receive_some. destruct msg. destruct m;
             inversion receive_some. cbn in *. destruct prev_state. unfold count.
             destruct count0; cbn; try reflexivity.
             inversion receive_some. rewrite <- H1. apply IH. rewrite <- H1 in H. apply H.
           -instantiate (DeployFacts := fun _ _ => True).
             instantiate (CallFacts := fun _ _ _ => True).
             instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
             unset_all; subst; cbn in *.
             destruct_chain_step; auto.
             destruct_action_eval; auto.
    Qed.
    
    Lemma no_calls bstate caddr :
      reachable bstate ->
      env_contracts bstate caddr = Some (Counter.contract : WeakContract) ->
      (outgoing_acts bstate caddr) = [].
    Proof. contract_induction; intros; cbn in *; auto.
           - inversion IH.
           - unfold receive in receive_some.
             destruct_match in receive_some; try congruence.
             destruct_match in receive_some; try congruence.
             inversion receive_some. rewrite IH. rewrite app_nil_r. reflexivity.
             + inversion receive_some. rewrite IH. rewrite app_nil_r. reflexivity.
           - unfold receive in receive_some.
             destruct_match in receive_some; try congruence.
           - rewrite IH in perm. apply Permutation_nil in perm. apply perm.
           - instantiate (DeployFacts := fun _ _ => True).
             instantiate (CallFacts := fun _ _ _ => True).
             instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
             unset_all; subst; cbn in *.
             destruct_chain_step; auto.
             destruct_action_eval; auto.
    Qed.
           
    (** TODO : Prove that the number of incomming tick calls + setup = the counter value *)

    
