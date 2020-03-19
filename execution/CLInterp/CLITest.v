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
Require Import CLITranslate.
Require Import CLInterp.

Close Scope Z_scope.
Close Scope N_scope.
Close Scope nat_scope.
Close Scope positive.

(** TODO: Not really working, i need a crash course in notation *)
(** (Danil) Fixed the notation a bit *)
Notation "a - b" := (OpE Sub [a;b]) : cl_scope.
Notation "a < b" := (OpE Less [a;b]) : cl_scope.
Notation "'obsB(' z1 ';' z2 ')'" := (Obs (LabB z1) z2) (at level 100, right associativity) : cl_scope.
Notation "'lbB(' z1 ')'" := (LabB z1) : cl_scope.


Notation "'ifc' e 'within' n 'then' c1 'else' c2" := (If e n c1 c2) (at level 100, e at next level, right associativity).
Notation "'ifc' e 'then' c1 'else' c2" := (If e 0 c1 c2) (at level 100, e at next level, right associativity).
Notation "'Ø'" := Zero.
Notation "e × c" := (Scale e c) (at level 100, right associativity).
Notation "c '(|' p1 '--->' p2 '|)'" := (Transfer p1 p2 c)(at level 50, right associativity).
Notation "d ↑ c" := (Translate d c)(at level 100, right associativity).
Notation "c1 & c2" := (Both c1 c2)(at level 100).

Open Scope Z_scope.
(** Equivalent example environments for CL and CLVM *)
Definition ext_exmp1 := update_ext (LabZ 1) 4 (ZVal 20) (update_ext (LabB 0) 4 (BVal true) (update_ext (LabZ 2) 1 (ZVal (-4)) (update_ext (LabZ 1) 0 (ZVal 1) (update_ext  (LabZ 1) 1 (ZVal 2) def_ext )))).
Definition extm_exmp1 : FMap (ObsLabel * Z) Val := FMap.add ((LabZ 1),4) (ZVal 20) (FMap.add ((LabB 0),4) (BVal true) (FMap.add ((LabZ 2),1) (ZVal (-4)) (FMap.add ((LabZ 1),0) (ZVal 1) (FMap.add ((LabZ 1),1) (ZVal 2) def_extM)))).

Compute ext_exmp1 (LabB 0) 4.

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

Open Scope cl_scope.

Definition c_exmp1 := (Scale obs1 (Transfer (PartyN 1) (PartyN 2) DKK)).
Definition c_exmp1' := obs1 × (DKK (|p1 ---> p2|)).
Definition c_exmp2 := (Translate 1 (Scale obs2 (Transfer (PartyN 1) (PartyN 2) DKK))).
Definition c_exmp2' := (1 ↑ (obs2 × DKK (| p1 ---> p2|))).

Definition c_exmp3 := (Both c_exmp1 c_exmp2).
Definition c_exmp3' := c_exmp1 & c_exmp2.

Definition c_exmp4 := Translate 1 (Both ((Scale obs1 (Transfer (PartyN 1) (PartyN 2) DKK))) (Scale obs2 (Transfer (PartyN 1) (PartyN 2) DKK))).
Definition c_exmp4' := 1 ↑ ((obs1 × DKK (| p1 ---> p2 |)) &
                             (obs2 × DKK (| p1 ---> p2 |))).

Definition std_option := ifc obs_bool within 30 then c_exmp1 else Ø.
Definition over_price := OpE Leq [obs1 ; OpE Mult [VarE V1; (OpE (ZLit 2) [])]].
Definition let_option := Let obs1 (ifc over_price within 30 then Ø else c_exmp1).


Definition AAPL := 0%Z.

(** An european call option. *)
(** Note that the decision of whether to "execute" the option is build-in into the contract.If the price of AAPL stock is greater then the [strike], then the difference between the actual price and the strike price is trasferred from [p1] to [p2].
 Basically it's the same as buying the [APPL] shares at the [strike] price and immediately selling them. *)
Definition european_option (maturity : nat) strike :=
  maturity ↑ (ifc (strike < obsB(AAPL;0))
               then (obsB(AAPL;0) - strike) × DKK(| p1 ---> p2 |)
               else Ø).

Compute lookupTrace (Csem c_exmp1 [] (ExtMap_to_ExtEnv extm_exmp1)) 0 p1 p2 DKK.
Compute lookupTraceM (CompileRunC c_exmp1 [] extm_exmp1) 0 p1 p2 DKK.

Compute lookupTrace (Csem std_option [] ext_exmp1) 1 p1 p2 DKK.
Compute lookupTrace (Csem let_option [] ext_exmp1) .

(** Since CL and CLVM expressions output the same type, we can write unit tests *)
Lemma test1 : (CompileRunE exmp1) = Esem exmp1 [] def_ext.
Proof. reflexivity. Qed.

Lemma test2 : (CompileRunE exmp2) = Esem exmp2 [] def_ext.
Proof. reflexivity. Qed.

Lemma test3 : (CompileRunE exmp3) = Esem exmp3 [] def_ext.
Proof. reflexivity. Qed.


(** TODO: How do we prove these? CL outputs functions and CLVM outputs finite maps *)

(** I think we should first get traces from both sides and then apply functional extensionality and show that they give the same values if applied to the same arguments. *)
Lemma c1 : (Csem c_exmp1 [] (ExtMap_to_ExtEnv extm_exmp1)) =
           liftM2 traceMtoTrace (CompileRunC c_exmp1 [] extm_exmp1) (Some 0) .
Proof. unfold traceMtoTrace,liftM2, c_exmp1,extm_exmp1. simpl. cbn.
       (* (Danil) it looks like FMap stuff doesn't compute very well. I don't have much experinece with this implementation of finite maps, maybe Jakobe can help. *)
       set (f := extm_exmp1).
Admitted.

(* Lemma c2 : (Csem c_exmp2 [] ext_exmp1) =  (CompileRunC c_exmp2 [] extm_exmp1). *)
(*   Proof. reflexivity. Qed. *)
(* pp *)
(*  Lemma c3 : (Csem c_exmp3 [] ext_exmp1) = (CompileRunC c_exmp3 [] extm_exmp1). *)
(* Proof. reflexivity. Qed. *)
(* Lemma c4 : (Csem c_exmp4 [] ext_exmp1) = (CompileRunC c_exmp4 [] extm_exmp1) . *)
(* Proof. reflexivity. Qed. *)
(* Lemma c5 : (Csem std_option [] ext_exmp1) = (CompileRunC std_option [] extm_exmp1). *)
(* Proof. reflexivity. Qed. *) *)

(** Test Code for scale transM
Definition p1 := PartyN 1.
Definition p2 := PartyN 2.
Definition p3 := PartyN 3.

Definition t1 := singleton_transM p1 p2 DKK 1.
Definition t2 := singleton_transM p2 p3 DKK 2.
Definition u12 := add_transM t1 t2.
Compute lookup_transM p1 p2 DKK (scale_transM 3 u12).
 *)


