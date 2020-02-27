From Coq Require Import List.
Import ListNotations.

Inductive unop :=
  | OSucc : unop
  | OPred : unop.

Inductive binop :=
  | OPlus : binop
  | OMult : binop.

Inductive exp :=
  | ENat : nat -> exp
  | EUnOp : unop -> exp -> exp
  | EBinOp : binop -> exp -> exp -> exp.

Definition eval_unop (u : unop) : nat -> nat :=
  match u with
  | OSucc => S
  | OPred => pred
  end.

Definition eval_binop (b : binop) : nat -> nat -> nat :=
  match b with
  | OPlus => Nat.add
  | OMult => Nat.mul
  end.

Fixpoint eval (e : exp) : nat :=
  match e with
  | ENat n => n
  | EUnOp u e => eval_unop u (eval e)
  | EBinOp b el er => eval_binop b (eval el) (eval er)
  end.

Inductive instruction :=
  | IPush : nat -> instruction
  | IUnOp : unop -> instruction
  | IBinOp : binop -> instruction.

Fixpoint compile (e : exp) : list instruction :=
  match e with
  | ENat n => [IPush n]
  | EUnOp u e => compile e ++ [IUnOp u]
  | EBinOp b el er => compile el ++ compile er ++ [IBinOp b]
  end.

Fixpoint decompile_aux (stack : list exp) (insts : list instruction) : option (list exp) :=
  match insts with
  | [] => Some stack
  | inst :: insts =>
    match inst with
    | IPush n => decompile_aux (ENat n :: stack) insts 
    | IUnOp u =>
      match stack with
      | [] => None
      | arg :: tl => decompile_aux (EUnOp u arg :: tl) insts 
      end
    | IBinOp b =>
      match stack with
      | argr :: argl :: tl => decompile_aux (EBinOp b argl argr :: tl) insts 
      | _ => None
      end
    end
  end.

Definition decompile (insts : list instruction) : option exp :=
  match decompile_aux [] insts with
  | Some [x] => Some x
  | _ => None
  end.

Lemma decompile_aux_correct e s tl :
  decompile_aux s (compile e ++ tl) = decompile_aux (e :: s) tl.
Proof.
  revert s tl.
  induction e as [n|u e IH|u el IHl er IHr]; intros s tl; auto; cbn in *.
  - now rewrite <- app_assoc, IH.
  - now rewrite <- 2!app_assoc, IHl, IHr.
Qed.

Lemma decompile_correct e :
  decompile (compile e) = Some e.
Proof.
  unfold decompile.
  now rewrite <- (app_nil_r (compile e)), decompile_aux_correct.
Qed.

Definition vm (insts : list instruction) : option nat :=
  match decompile insts with
  | Some e => Some (eval e)
  | None => None
  end.

Lemma vm_correct e :
  vm (compile e) = Some (eval e).
Proof.
  unfold vm.
  now rewrite decompile_correct.
Qed.

Lemma decompile_aux_structure s1 is s2 :
  decompile_aux s1 is = Some s2 ->
  concat (map (fun e => rev (compile e)) s2) = rev is ++ concat (map (fun e => rev (compile e)) s1).
Proof.
  revert s1 s2.
  induction is as [|i is IH]; intros s1 s2; cbn in *.
  - intros eq. inversion_clear eq. auto.
  - destruct i.
    + intros H.
      specialize (IH _ _ H).
      rewrite IH.
      rewrite <- app_assoc.
      f_equal.
    + destruct s1; try congruence.
      intros H.
      specialize (IH _ _ H).
      rewrite IH.
      rewrite <- app_assoc.
      cbn.
      now rewrite rev_app_distr.
    + destruct s1; try congruence.
      destruct s1; try congruence.
      intros H.
      specialize (IH _ _ H).
      rewrite IH.
      rewrite <- app_assoc.
      cbn.
      rewrite 2!rev_app_distr.
      cbn.
      now rewrite <- app_assoc.
Qed.

Lemma compile_decompile insts e :
  decompile insts = Some e -> compile e = insts.
Proof.
  unfold decompile.
  intros decomp_eq.
  destruct (decompile_aux _ _) eqn:decomp; try congruence.
  destruct l; try congruence.
  destruct l; try congruence.
  inversion decomp_eq; subst; clear decomp_eq.
  pose proof (decompile_aux_structure _ _ _ decomp).
  cbn in H.
  rewrite 2!app_nil_r in H.
  now rewrite <- rev_involutive, <- H, rev_involutive.
Qed.
