From Coq Require Import PeanoNat ZArith Notations Bool.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker SafeTemplateChecker.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Extraction Require Import LPretty Certified Extra.
From ConCert.Execution Require Import Containers.
From ConCert.CL Require Import CLIPrelude.
From ConCert.CL Require Import CLITranslate.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.


Definition PREFIX := "".

Definition params := list instruction * Env * ExtMap * bool.

Definition receive (p : params) := StackEInterp p.1.1.1 [] p.1.1.2 p.1.2 p.2.

Definition local_def := local PREFIX.

Definition print_finmap_type (prefix ty_key ty_val : string) :=
  parens false (ty_key ++ "," ++ prefix ++ ty_val) ++ " map".

(** A translation table for various constants we want to rename *)

Definition TT : env string :=
  [   (* remapping types *)
    remap <% Z %> "int"
    ; remap <% bool %> "bool"
    ; remap <% nat %> "address"
    ; remap <% list %> "list"
    ; remap <% string %> "string"

    (* remapping operations *)
    ; remap <% Z.add %> "addInt"
    ; remap <% Z.eqb %> "eqInt"
    (*; remap <% @lookup %> "Map.find"*)
    ; remap <% @fst %> "fst"
    ; remap <% @snd %> "snd"
    ; remap <% andb %> "andb"
    (* remapping constructors *)
    ; ("Some", "Some")
    ; ("None", "None")
    ; ("true", "true")
    ; ("false", "false")
    ; ("Z0" ,"0")
    ; ("nil", "[]")

    (* local types *)
    ; local_def <% params %>
    ; local_def <% StackEInterp %>
    ; local_def <% instruction %>
    ; local_def <% Val %>
    ; local_def <% Op %>
  ].

Definition print_main (func_name : string): string :=
  let func_name := PREFIX ++ func_name in
  let params_name := PREFIX ++ "params" in
  "let%entry main (p : " ++ params_name ++ ")" ++ " s ="
    ++ nl
    ++ "match " ++ func_name ++ " p s"  ++ " with"
    ++ nl
    ++ "| Some res -> ( [], res ) "
    ++ nl
    ++ "| _ -> Current.failwith s".

Fixpoint combine_global_envs (Σ Σ' : global_env) : global_env :=
  match Σ' with
  | [] => Σ
  | (nm,d) :: Σ'' => match (lookup_env Σ nm) with
                   | Some _ => (combine_global_envs Σ Σ'')%list
                   | None => ((nm,d) :: combine_global_envs Σ Σ'')%list
                   end
  end.

Definition INTERP_MODULE : LiquidityModule :=
  {| (* a name for the definition with the extracted code *)
     lm_module_name := "liquidity_stack_interp" ;

     (* definitions of operations on ints, bools, pairs, ect. *)
     lm_prelude := prod_ops ++ nl ++ int_ops ++ nl ++ bool_ops;

     (* inductives *)
     lm_adts := ["Op";"instruction";"Val"];

     (* definitions: type abbreviations and functions *)
     lm_defs := ["params";"StackEInterp";"receive"];

     (* code for the entry point *)
     lm_entry_point := print_main "receive";

     (* initial storage *)
     lm_init := "[]" |}.


Run TemplateProgram (ps <- monad_map erasable_program (List.rev INTERP_MODULE.(lm_defs)) ;;
                     let env := fold_left combine_global_envs (map fst ps) [] in
                     res <- tmEval all env ;;
                     tmDefinition "GE" res).
