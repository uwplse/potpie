From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DanTrick.StackLanguage DanTrick.StackLangTheorems DanTrick.StackLangEval DanTrick.LogicProp DanTrick.StackLogicGrammar DanTrick.StackExprWellFormed.

(* Now we want to be able to express when you have the stack change size *)

Fixpoint aexp_stack_size_inc (inc: nat) (a: aexp_stack): aexp_stack :=
  match a with
  | Var_Stk k => Var_Stk (k + inc)
  | Plus_Stk a1 a2 => Plus_Stk (aexp_stack_size_inc inc a1)
                              (aexp_stack_size_inc inc a2)
  | Minus_Stk a1 a2 => Minus_Stk (aexp_stack_size_inc inc a1)
                                (aexp_stack_size_inc inc a2)
  | App_Stk f args => App_Stk f (map (aexp_stack_size_inc inc) args)
  | _ => a
  end.

Fixpoint bexp_stack_size_inc (inc: nat) (b: bexp_stack): bexp_stack :=
  match b with
  | Neg_Stk b' => Neg_Stk (bexp_stack_size_inc inc b')
  | And_Stk b1 b2 => And_Stk (bexp_stack_size_inc inc b1)
                            (bexp_stack_size_inc inc b2)
  | Or_Stk b1 b2 => Or_Stk (bexp_stack_size_inc inc b1)
                          (bexp_stack_size_inc inc b2)
  | Leq_Stk a1 a2 => Leq_Stk (aexp_stack_size_inc inc a1)
                            (aexp_stack_size_inc inc a2)
  | Eq_Stk a1 a2 => Eq_Stk (aexp_stack_size_inc inc a1)
                          (aexp_stack_size_inc inc a2)
  | _ => b
  end.

Definition meta_stack_size_inc (inc: nat) (m: MetavarPred): MetavarPred :=
  match m with
  | MetaBool b => MetaBool (transform_prop_exprs b (bexp_stack_size_inc inc))
  | MetaNat a => MetaNat (transform_prop_exprs a (aexp_stack_size_inc inc))
  end.

Definition absstack_stack_size_inc (inc: nat) (a: AbsStack): AbsStack :=
  match a with
  | AbsStkTrue => AbsStkSize inc
  | AbsStkSize n => AbsStkSize (n + inc)
  end.

Fixpoint absstate_stack_size_inc (inc: nat) (a: AbsState): AbsState :=
  let recur := absstate_stack_size_inc inc in
  match a with
  | BaseState s m =>
      BaseState (absstack_stack_size_inc inc s)
                (meta_stack_size_inc inc m)
  | AbsAnd a1 a2 =>
      AbsAnd (recur a1) (recur a2)
  | AbsOr a1 a2 =>
      AbsOr (recur a1) (recur a2)
  end.

Inductive aexp_stk_size_inc_rel: nat -> aexp_stack -> aexp_stack -> Prop :=
| IncConstStk :
  forall (inc: nat) (n: nat),
    aexp_stk_size_inc_rel inc (Const_Stk n) (Const_Stk n)
| IncVarstk :
  forall (inc: nat) (k: stack_index),
    aexp_stk_size_inc_rel inc (Var_Stk k) (Var_Stk (k + inc))
| IncPlusStk :
  forall (inc: nat) (a1 a2 a1' a2': aexp_stack),
    aexp_stk_size_inc_rel inc a1 a1' ->
    aexp_stk_size_inc_rel inc a2 a2' ->
    aexp_stk_size_inc_rel inc (Plus_Stk a1 a2) (Plus_Stk a1' a2')
| IncMinusStk :
  forall (inc: nat) (a1 a2 a1' a2': aexp_stack),
    aexp_stk_size_inc_rel inc a1 a1' ->
    aexp_stk_size_inc_rel inc a2 a2' ->
    aexp_stk_size_inc_rel inc (Minus_Stk a1 a2) (Minus_Stk a1' a2')
| IncAppStk :
  forall (inc: nat) (f: ident) (args args': list aexp_stack),
    args_stk_size_inc_rel inc args args' ->
    aexp_stk_size_inc_rel inc (App_Stk f args) (App_Stk f args')
with args_stk_size_inc_rel : nat -> (list aexp_stack) -> (list aexp_stack) -> Prop :=
| IncArgsStkNil :
  forall (inc: nat),
    args_stk_size_inc_rel inc nil nil
| IncArgsStkCons :
  forall (inc: nat) (arg arg': aexp_stack) (args args': list aexp_stack),
    aexp_stk_size_inc_rel inc arg arg' ->
    args_stk_size_inc_rel inc args args' ->
    args_stk_size_inc_rel inc (arg :: args) (arg' :: args').

Scheme aexp_stk_size_inc_rel_mut_ind := Induction for aexp_stk_size_inc_rel Sort Prop
    with args_stk_size_inc_rel_mut_ind := Induction for args_stk_size_inc_rel Sort Prop.

Combined Scheme aexp_args_size_inc_rel_mut_ind from aexp_stk_size_inc_rel_mut_ind, args_stk_size_inc_rel_mut_ind.

Definition aexp_args_size_inc_rel_mut_ind_theorem (P: nat -> aexp_stack -> aexp_stack -> Prop) (P0: nat -> list aexp_stack -> list aexp_stack -> Prop): Prop :=
  (forall (n: nat) (a a': aexp_stack),
      aexp_stk_size_inc_rel n a a' ->
      P n a a') /\
    (forall (n: nat) (l l': list aexp_stack),
        args_stk_size_inc_rel n l l' ->
        P0 n l l').

Definition aexp_args_size_inc_rel_mut_ind_theorem_P (P: nat -> aexp_stack -> aexp_stack -> Prop) : forall (n : nat) (a a0 : aexp_stack), aexp_stk_size_inc_rel n a a0 -> Prop :=
  fun (n: nat) (a a': aexp_stack) =>
  fun (_: aexp_stk_size_inc_rel n a a') =>
    P n a a'.

Definition aexp_args_size_inc_rel_mut_ind_theorem_P0 (P0: nat -> list aexp_stack -> list aexp_stack -> Prop): forall (n : nat) (l l0 : list aexp_stack), args_stk_size_inc_rel n l l0 -> Prop :=
  fun (n: nat) (l l0 : list aexp_stack) =>
  fun (H: args_stk_size_inc_rel n l l0) =>
    P0 n l l0.

Ltac aexp_args_size_inc_rel_mutual_induction P P0 P_def P0_def :=
  pose (aexp_args_size_inc_rel_mut_ind_theorem_P P_def) as P;
  pose (aexp_args_size_inc_rel_mut_ind_theorem_P0 P0_def) as P0;
  apply (aexp_args_size_inc_rel_mut_ind P P0); unfold P, P0; unfold aexp_args_size_inc_rel_mut_ind_theorem_P, aexp_args_size_inc_rel_mut_ind_theorem_P0; unfold P_def, P0_def.

Local Definition preserves_wf_P (n: nat) (a a': aexp_stack): Prop :=
  aexp_well_formed a ->
  aexp_well_formed a'.

Local Definition preserves_wf_P0 (n: nat) (args args': list aexp_stack): Prop :=
  args_well_formed args ->
  args_well_formed args'.

Theorem aexp_args_size_inc_preserves_wf :
  aexp_args_size_inc_rel_mut_ind_theorem preserves_wf_P preserves_wf_P0.
Proof.
  aexp_args_size_inc_rel_mutual_induction P P0 preserves_wf_P preserves_wf_P0; intros.
  - assumption.
  - invs H. constructor. intuition.
  - invs H1. econstructor.
    + eapply H. assumption.
    + eapply H0; assumption.
  - invs H1; econstructor; [eapply H | eapply H0]; eassumption.
  - invs H0. econstructor. apply H; assumption.
  - assumption.
  - invs H1. econstructor; [eapply H | eapply H0]; eassumption.
Qed.

Lemma aexp_size_inc_preserves_wf :
  forall inc a a',
    aexp_stk_size_inc_rel inc a a' ->
    aexp_well_formed a ->
    aexp_well_formed a'.
Proof.
  pose proof aexp_args_size_inc_preserves_wf.
  unfold preserves_wf_P, preserves_wf_P0 in H.
  unfold aexp_args_size_inc_rel_mut_ind_theorem in H.
  destruct H; auto.
Qed.

Lemma args_size_inc_preserves_wf :
  forall inc args args',
    args_stk_size_inc_rel inc args args' ->
    args_well_formed args ->
    args_well_formed args'.
Proof.
  pose proof aexp_args_size_inc_preserves_wf.
  unfold preserves_wf_P, preserves_wf_P0 in H.
  unfold aexp_args_size_inc_rel_mut_ind_theorem in H.
  destruct H; auto.
Qed.

Inductive bexp_stk_size_inc_rel : nat -> bexp_stack -> bexp_stack -> Prop :=
| IncTrueStk :
  forall (inc: nat),
    bexp_stk_size_inc_rel inc (True_Stk) (True_Stk)
| IncFalseStk :
  forall (inc: nat),
    bexp_stk_size_inc_rel inc (False_Stk) (False_Stk)
| IncNegStk :
  forall (inc: nat) (b b': bexp_stack),
    bexp_stk_size_inc_rel inc b b' ->
    bexp_stk_size_inc_rel inc (Neg_Stk b) (Neg_Stk b')
| IncAndStk :
  forall (inc: nat) (b1 b2 b1' b2': bexp_stack),
    bexp_stk_size_inc_rel inc b1 b1' ->
    bexp_stk_size_inc_rel inc b2 b2' ->
    bexp_stk_size_inc_rel inc (And_Stk b1 b2) (And_Stk b1' b2')
| IncOrStk :
  forall (inc: nat) (b1 b2 b1' b2': bexp_stack),
    bexp_stk_size_inc_rel inc b1 b1' ->
    bexp_stk_size_inc_rel inc b2 b2' ->
    bexp_stk_size_inc_rel inc (Or_Stk b1 b2) (Or_Stk b1' b2')
| IncLeqStk :
  forall (inc: nat) (a1 a2 a1' a2': aexp_stack),
    aexp_stk_size_inc_rel inc a1 a1' ->
    aexp_stk_size_inc_rel inc a2 a2' ->
    bexp_stk_size_inc_rel inc (Leq_Stk a1 a2) (Leq_Stk a1' a2')
| IncEqStk :
  forall (inc: nat) (a1 a2 a1' a2': aexp_stack),
    aexp_stk_size_inc_rel inc a1 a1' ->
    aexp_stk_size_inc_rel inc a2 a2' ->
    bexp_stk_size_inc_rel inc (Eq_Stk a1 a2) (Eq_Stk a1' a2').

Lemma bexp_size_inc_preserves_wf :
  forall inc b b',
    bexp_stk_size_inc_rel inc b b' ->
    bexp_well_formed b ->
    bexp_well_formed b'.
Proof.
  intros inc b b' H. induction H; intros; auto.
  - invs H0. econstructor; eauto.
  - invs H1. econstructor; eauto.
  - invs H1. econstructor; eauto.
  - invs H1. econstructor; eauto; eapply aexp_size_inc_preserves_wf; eauto.
  - invs H1. econstructor; eauto; eapply aexp_size_inc_preserves_wf; eauto.
Qed.

Inductive meta_stk_size_inc : nat -> MetavarPred -> MetavarPred -> Prop :=
| IncMetaBool :
  forall inc b b',
    transformed_prop_exprs (bexp_stk_size_inc_rel inc) b b' ->
    prop_rel bexp_well_formed b ->
    meta_stk_size_inc inc (MetaBool b) (MetaBool b')
| IncMetaNat :
  forall inc a a',
    transformed_prop_exprs (aexp_stk_size_inc_rel inc) a a' ->
    prop_rel aexp_well_formed a ->
    meta_stk_size_inc inc (MetaNat a) (MetaNat a').

Inductive absstack_stk_size_inc : nat -> AbsStack -> AbsStack -> Prop :=
| IncAbsStkTrue :
  forall inc,
    absstack_stk_size_inc inc AbsStkTrue (AbsStkSize inc)
| IncAbsStkSize :
  forall inc size,
    absstack_stk_size_inc inc (AbsStkSize size) (AbsStkSize (size + inc)).

Inductive state_stk_size_inc : nat -> AbsState -> AbsState -> Prop :=
| IncBaseState :
  forall inc s s' m m',
    absstack_stk_size_inc inc s s' ->
    meta_stk_size_inc inc m m' ->
    state_stk_size_inc inc (BaseState s m) (BaseState s' m')
| IncAbsAnd :
  forall inc s1 s2 s1' s2',
    state_stk_size_inc inc s1 s1' ->
    state_stk_size_inc inc s2 s2' ->
    state_stk_size_inc inc (AbsAnd s1 s2) (AbsAnd s1' s2')
| IncAbsOr :
  forall inc s1 s2 s1' s2',
    state_stk_size_inc inc s1 s1' ->
    state_stk_size_inc inc s2 s2' ->
    state_stk_size_inc inc (AbsOr s1 s2) (AbsOr s1' s2').
