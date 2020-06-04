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

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.


Definition PREFIX := "".

Inductive Op : Set := Add | Sub | Mult | Div | And | Or | Less | Leq | Equal |
                      Not | Neg |
                      BLit (b : bool) | ZLit (r : Z) |
                      Cond.

Close Scope Z.

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

Definition params := list instruction * Env * ExtMap.

Definition find_default (k : (ObsLabel * Z)) (ext : ExtMap) (default : Val) : Val := match (FMap.find k ext) with
                                                                                     | None => default
                                                                                     | Some v => v
                                                                                     end.

Definition lookup (k : ObsLabel * Z) (ext : ExtMap) := FMap.find k ext.

Open Scope Z.

Fixpoint StackEInterp (instrs : list instruction) (stack : list (option Val)) (env: Env) (ext: ExtMap) : option Val :=
  match instrs with
  | [] => match stack with [val] => val | _ => None end
  | hd::tl =>
    match hd with
    | IPushZ z => StackEInterp tl ((Some (ZVal z))::stack) env ext
    | IPushB b => StackEInterp tl ((Some (BVal b))::stack) env ext
    | IObs l i => StackEInterp tl ((lookup (l,i) ext)::stack) env ext
    | IOp op => match op with
               | Add => match stack with
                       | (Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                        StackEInterp tl (Some (ZVal (z1 + z2))::tl2) env ext
                       | _ => None
                       end
               | Sub => match stack with
                       | (Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                         StackEInterp tl (Some (ZVal (z1 - z2))::tl2) env ext
                       | _ => None
                       end
               | Mult => match stack with
                        | (Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                          StackEInterp tl (Some (ZVal (z1 * z2))::tl2) env ext
                        | _ => None
                        end
               | Div => match stack with
                       | (Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                        StackEInterp tl (Some (ZVal (z1 / z2))::tl2) env ext
                       | _ => None
                       end
               | And => match stack with (Some (BVal b1))::(Some (BVal b2))::tl2 =>
                                        StackEInterp tl (Some (BVal (b1 && b2))::tl2) env ext  | _ => None
                       end
               | Or => match stack with
                      |(Some (BVal b1))::(Some (BVal b2))::tl2 =>
                       StackEInterp tl (Some (BVal (b1 || b2))::tl2) env ext
                      | _ => None
                      end
               | Less => match stack with
                        |(Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                         StackEInterp tl (Some (BVal (z1 <? z2))::tl2) env ext
                        | _ => None
                        end
               | Leq => match stack with
                       |(Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                        StackEInterp tl (Some (BVal (z1 <=? z2))::tl2) env ext
                       | _ => None
                        end
               | Equal => match stack with
                           | (Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                             StackEInterp tl (Some (BVal (z1 =? z2))::tl2) env ext
                           | _ => None
                         end
               | Cond => match stack with
                        | (Some (BVal b))::(Some (ZVal z1))::(Some (ZVal z2))::tl2 =>
                          StackEInterp tl ((Some (ZVal (if b then z1 else z2)))::tl2) env ext
                        | (Some (BVal b))::(Some (BVal b1))::(Some (BVal b2))::tl2 =>
                          StackEInterp tl ((Some (BVal (if b then b1 else b2)))::tl2) env ext
                        | _ => None
                        end
               | Not => match stack with
                       | ((Some (BVal b))::tl2) => StackEInterp tl ((Some (BVal (negb b)))::tl2) env ext
                       | _ => None end
               | Neg => match stack with
                       | ((Some (ZVal z))::tl2) => StackEInterp tl ((Some (ZVal (0 -z)))::tl2) env ext
                       | _ => None end
               | _ => None 
               end
    | IVar n => match (StackLookupEnv n env) with
               | Some v => StackEInterp tl ((Some v)::stack) env ext
               | None => None
               end
    | IAccStart1 z => StackEInterp tl stack env (adv_map (-z) ext)
    | IAccStart2 => match stack with (Some v)::tl2 => StackEInterp tl tl2 (v::env) (adv_map 1 ext) | _ => None end
    | IAccStep => match stack with (Some v)::tl2 => let env' := List.tl env in
                                                 StackEInterp tl tl2 (v::env') (adv_map 1 ext)  | _ => None end
    | IAccEnd => StackEInterp tl stack (List.tl env) ext
    end
  end.


Definition receive (p : params) := StackEInterp p.1.1 [] p.1.2 p.2.

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
    ; remap <% @lookup %> "Map.find"
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
    
    ; local_def <% StackEInterp %>
    ; local_def <% params %>
    ; local_def <% instruction %>
    ; local_def <% Op %>
    ; local_def <% Val %>
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

Time Run TemplateProgram (printLiquidityModule PREFIX GE TT INTERP_MODULE).

Print liquidity_stack_interp.
