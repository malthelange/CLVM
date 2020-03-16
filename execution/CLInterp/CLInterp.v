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

Open Scope Z.

Set Nonrecursive Elimination Schemes.

Section Interp.
  Context `{Base : ChainBase}.


  Record Setup :=
    build_setup {
        setup_contract : list CInstruction;
      }.

  Record State :=
    build_state {
        contract : list CInstruction;
        currentTime : nat;
        result : option TraceM;
      }.

  Inductive Msg :=
  | update : ExtMap -> nat -> Msg.                          


  Instance party_serializable : Serializable Party :=
    Derive Serializable Party_rect<PartyN>.
  Instance Obs_serializable : Serializable ObsLabel :=
    Derive Serializable ObsLabel_rect<LabZ, LabB>.
  Instance Val_Serializable : Serializable Val :=
    Derive Serializable Val_rect<BVal, ZVal>.
  Instance ExtMapSerializable : Serializable ExtMap := _.
  Instance asset_serializable : Serializable Asset :=
    Derive Serializable Asset_rect<DKK, USD>.
  Instance TransSerial : Serializable TransM := _.
  Instance TraceSerial : Serializable TraceM := _.
  Instance Op_serializable : Serializable Op :=
    Derive Serializable Op_rect <Add, Sub, Mult, Div, And, Or, Less, Leq, Equal, Not, Neg, BLit, ZLit, Cond>.
  Instance instruction_serializable : Serializable instruction :=
    Derive Serializable instruction_rect<IPushZ, IPushB, IObs, IOp, IAcc, IVar>.
   Instance Env_Serializable : Serializable Env := _.
  Instance CInstruction_serializable : Serializable CInstruction := 
    Derive Serializable CInstruction_rect< CIZero, CITransfer, CIScale, CIBoth, CITranslate, CILet, CIIf>.
  Instance SetupSerial : Serializable Setup :=
    Derive Serializable Setup_rect<build_setup>.
  Instance StateSerial : Serializable State :=
    Derive Serializable State_rect<build_state>.
  Instance MsgSerial : Serializable Msg :=
    Derive Serializable Msg_rect<update>.
  Global Instance State_settable : Settable _ :=
    settable! build_state <contract; currentTime; result>.
  
  Definition init (chain : Chain) (ctx: ContractCallContext) (setup: Setup) : option State :=
    let contract := setup_contract setup in
    Some (build_state contract 0 None).

  Definition receive
             (chain : Chain) (ctx : ContractCallContext)
             (state : State) (msg : option Msg)
    : option (State * list ActionBody) :=
    match msg with
    | Some (update ext t) => Some (state<|result := (vmC (contract state) [] ext)|>, [])
    | None => Some (state,[])
    end.
End Interp.
