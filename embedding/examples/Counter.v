Require Import String ZArith Basics.
From ConCert Require Import Ast Notations PCUICTranslate PCUICtoTemplate.
From ConCert Require Import Utils Prelude SimpleBlockchain CustomTactics.
Require Import List PeanoNat ssrbool.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import BaseTypes.
Open Scope list.

Import AcornBlockchain.

Import Lia.

Run TemplateProgram
      (mkNames ["State" ; "mkState"; "count"; "dummy";
                "Res" ; "Error";
                "Msg"; "Tick"; "NOP";
               "Action"; "Transfer"; "Empty" ] "_coq").

Import ListNotations.

Definition state_syn : global_dec :=
  [\ record State := mkState { count : Nat ; 
                               dummy : Bool} \].

Set Nonrecursive Elimination Schemes.
Make Inductive (global_to_tc state_syn).

Definition msg_syn :=
  [\ data Msg =
   Tick [_] |
   NOP [_] \].

Make Inductive (global_to_tc msg_syn).

Print Msg_coq.

  Notation "'Tick'" :=
    (pConstr Tick []) ( in custom pat at level 0).
  Notation "'NOP'" :=
    (pConstr NOP []) ( in custom pat at level 0).

  Notation "'Just' x" :=
    (pConstr "Some" [x]) (in custom pat at level 0,
                             x constr at level 4).
  Notation "'Nothing'" := (pConstr "None" [])
                            (in custom pat at level 0).
  (** Projections *)
  Notation "'count' a" :=
    [| {eConst count} {a} |]
      (in custom expr at level 0).
  
  Notation "'dummy' a" :=
    [| {eConst dummy} {a} |]
      (in custom expr at level 0).

  Notation "'Nil'" := [| {eConstr "list" "nil"} {eTy (tyInd SActionBody)} |]
                        (in custom expr at level 0).
 
  Notation " x ::: xs" := [| {eConstr "list" "cons"} {eTy (tyInd SActionBody)} {x} {xs} |]
                            ( in custom expr at level 0).

  Notation "[ x ]" := [| {eConstr "list" "cons"} {eTy (tyInd SActionBody)} {x} Nil |]
                        ( in custom expr at level 0,
                             x custom expr at level 1).

 Definition actions_ty := [! "list" "SimpleActionBody" !].

  Notation "'Result'" := [!"prod" State ("list" "SimpleActionBody") !]
                           (in custom type at level 2).

  Notation "'Just' a" := [| {eConstr "option" "Some"}  {eTy [! Result!]} {a}|]
                           (in custom expr at level 0,
                               a custom expr at level 1).

  Notation "'Pair' a b" := [| {eConstr "prod" "pair"}
                               {eTy (tyInd State)}
                               {eTy actions_ty} {a} {b} |]
                           (in custom expr at level 0,
                               a custom expr at level 1,
                               b custom expr at level 1).


  Definition mk_res a b := [| {eConstr "option" "Some"}
                                {eTy [! Result !]}
                                 ({eConstr "prod" "pair"} {eTy (tyInd State)}
                                 {eTy actions_ty} {a} {b}) |].
  Notation "'Res' a b" := (mk_res a b)
      (in custom expr at level 2,
          a custom expr at level 4,
          b custom expr at level 4).

  Notation "'Nothing'" := (eApp (eConstr "option" "None") (eTy [!Result!]))
                      (in custom expr at level 0).

  Notation "'mkState' a b" :=
    [| {eConstr State "mkState_coq"} {a} {b} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).

  Notation "'Transfer' a b" :=
    [| {eConstr SActionBody "Act_transfer"} {b} {a} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).

  Notation "'Empty'" := (eConstr Action Empty)
                      (in custom expr at level 0).

  Definition Σ' :=
    Prelude.Σ ++ [ Prelude.AcornMaybe;
           state_syn;
           msg_syn;
           addr_map_acorn;
           AcornBlockchain.SimpleChainAcorn;
           AcornBlockchain.SimpleContractCallContextAcorn;
           AcornBlockchain.SimpleActionBodyAcorn;
           gdInd "Z" 0 [("Z0", []); ("Zpos", [(None,tyInd "positive")]);
                          ("Zneg", [(None,tyInd "positive")])] false].

  Notation "0 'z'" := (eConstr "Z" "Z0") (in custom expr at level 0).

  Import Prelude.
  (** Generating string constants for variable names *)

  Run TemplateProgram (mkNames ["c";"s";"e";"m";"v";"dl"; "g"; "chain";
                              "tx_amount"; "bal"; "sender"; "own"; "isdone" ;
                              "accs"; "now";
                               "newstate"; "newmap"; "cond"] "").
  (** A shortcut for [if .. then .. else ..]  *)
  Notation "'if' cond 'then' b1 'else' b2 : ty" :=
    (eCase (Bool,[]) ty cond
           [(pConstr true_name [],b1);(pConstr false_name [],b2)])
      (in custom expr at level 4,
          cond custom expr at level 4,
          ty custom type at level 4,
          b1 custom expr at level 4,
          b2 custom expr at level 4).

  Notation SCtx := "SimpleContractCallContext".
  Definition test := [| 1 |].
  Unset Printing Notations.
  Print test.
  Make Definition test_coq :=
        (expr_to_tc Σ' (indexify nil test)).
      Print test_coq.
  Set Printing Notations.
  
  Module CrowdfundingContract.
    Import AcornBlockchain.
    Module Init.
      Import Notations.
          Definition crowdfunding_init : expr :=
            [| \c : SCtx => \dl : Nat => \g : Money => mkState dl False|].
          Make Definition init :=
            (expr_to_tc Σ' (indexify nil crowdfunding_init)).
          Check init.
    End Init.
    Module Receive.
      Import Notations.
      Import Prelude.
      
      Notation SCtx := "SimpleContractCallContext".
      Notation SChain := "SimpleChain".
      Definition counter : expr :=
        [| \chain : SChain =>  \c : SCtx => \m : Msg => \s : State =>
           case m : Msg return Maybe Result of
            | Tick ->
              Just (Pair (mkState (Suc(count s)) False) Nil )
            | NOP -> Just (Pair s Nil )
            |].
      Compute (expr_to_tc Σ' (indexify nil counter)).
      Make Definition receive :=
        (expr_to_tc Σ' (indexify nil counter)).
      Print receive.
    End Receive.


