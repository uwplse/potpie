From Coq Require Import Arith String List Psatz.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

From Imp_LangTrick.Stack Require Import StackLanguage StackLangTheorems StackLogicGrammar StackIncrease.
From Imp_LangTrick.LogicProp Require Import LogicProp LogicPropTheorems.

Lemma aexp_stack_size_inc_adequacy_forward :
  forall (inc: nat) (a a': aexp_stack),
    a' = aexp_stack_size_inc inc a ->
    aexp_stk_size_inc_rel inc a a'.
Proof.
  intros inc a.
  revert inc.
  eapply aexp_stack_ind2 with (P := fun a => forall inc a',
                                        a' = aexp_stack_size_inc inc a ->
                                        aexp_stk_size_inc_rel inc a a');
    simpl; intros; subst; econstructor; eauto.
  - revert H. clear f. clear a.
    revert inc. induction aexps; simpl; intros.
    + econstructor.
    + invs H. econstructor; eauto.
Defined.

Section AexpArgsSizeInc.
  Let P (n: nat) (a a': aexp_stack): Prop :=
        a' = aexp_stack_size_inc n a.
  Let P0 (n: nat) (args args': list aexp_stack) : Prop :=
        args' = map (aexp_stack_size_inc n) args.
  
  Lemma aexp_args_stack_size_inc_adequacy_backward :
    aexp_args_size_inc_rel_mut_ind_theorem P P0.
  Proof using P P0.
    (* unfold aexp_args_size_inc_rel_mut_ind_theorem. unfold P. unfold P0. *)
    aexp_args_size_inc_rel_mutual_induction P' P0' P P0; clear P' P0'; clear P P0; simpl; intros; subst; reflexivity.
  Defined.

  Lemma aexp_stack_size_inc_adequacy_backward :
    (forall (n : nat) (a a' : aexp_stack),
        aexp_stk_size_inc_rel n a a' -> a' = aexp_stack_size_inc n a).
  Proof.
    eapply aexp_args_stack_size_inc_adequacy_backward.
  Defined.
  Lemma args_stack_size_inc_adequacy_backward :
    (forall (n : nat) (l l' : list aexp_stack),
        args_stk_size_inc_rel n l l' -> l' = map (aexp_stack_size_inc n) l).
  Proof.
    eapply aexp_args_stack_size_inc_adequacy_backward.
  Defined.
End AexpArgsSizeInc.



Lemma bexp_stack_size_inc_adequacy_forward :
  forall (inc: nat) (b b': bexp_stack),
    b' = bexp_stack_size_inc inc b ->
    bexp_stk_size_inc_rel inc b b'.
Proof.
  induction b; simpl; intros; subst; econstructor; eauto using aexp_stack_size_inc_adequacy_forward.
Defined.

Lemma bexp_stack_size_inc_adequacy_backward :
  forall (inc: nat) (b b': bexp_stack),
    bexp_stk_size_inc_rel inc b b' ->
    b' = bexp_stack_size_inc inc b.
Proof.
  induction b; simpl; intros; try invs H; try reflexivity; f_equal; eauto using aexp_stack_size_inc_adequacy_backward.
Defined.

Lemma meta_stack_size_inc_adequacy_backward :
  forall (inc: nat) (m m': MetavarPred),
    meta_stk_size_inc inc m m' ->
    m' = meta_stack_size_inc inc m.
Proof.
  destruct m; intros; invs H; simpl; f_equal; (eapply transform_prop_exprs_adequacy_backward; [ | eauto ]); intros; split;
    eauto using bexp_stack_size_inc_adequacy_forward, bexp_stack_size_inc_adequacy_backward, aexp_stack_size_inc_adequacy_forward, aexp_stack_size_inc_adequacy_backward.
Defined.

Theorem aexp_stack_size_inc_adequacy :
  forall (inc: nat) (a a': aexp_stack),
    a' = aexp_stack_size_inc inc a <->
      aexp_stk_size_inc_rel inc a a'.
Proof.
  intros; split; eauto using aexp_stack_size_inc_adequacy_forward, aexp_stack_size_inc_adequacy_backward.
Defined.

Theorem bexp_stack_size_inc_adequacy :
  forall (inc: nat) (b b': bexp_stack),
    b' = bexp_stack_size_inc inc b <->
      bexp_stk_size_inc_rel inc b b'.
Proof.
  intros; split; eauto using bexp_stack_size_inc_adequacy_backward, bexp_stack_size_inc_adequacy_forward.
Defined.

Definition construct_meta_stk_size_inc (inc: nat) (m: MetavarPred): option (meta_stk_size_inc inc m (meta_stack_size_inc inc m)) :=
  match m with
  | MetaBool b =>
      let b' := (transform_prop_exprs b (bexp_stack_size_inc inc)) in
      let trans_b' := transform_prop_exprs_adequacy_forward _ _ b b'
                                                      (bexp_stack_size_inc inc) (bexp_stk_size_inc_rel inc)
                                                      (bexp_stack_size_inc_adequacy inc)
                                                      (eq_refl b') in
      let p := construct_prop_rel StackExprWellFormed.bexp_well_formed
                                  b
                                  StackExprWellFormed.construct_bexp_well_formed in
      match p with
      | Some p' => Some (IncMetaBool inc b b' trans_b' p')
      | None => None
      end
  | MetaNat a =>
      let a' := transform_prop_exprs a (aexp_stack_size_inc inc) in
      let trans_a' := transform_prop_exprs_adequacy_forward _ _ a a'
                                                            (aexp_stack_size_inc inc)
                                                            (aexp_stk_size_inc_rel inc)
                                                            (aexp_stack_size_inc_adequacy inc)
                                                            (eq_refl a') in
      let p := construct_prop_rel StackExprWellFormed.aexp_well_formed
                                  a
                                  StackExprWellFormed.construct_aexp_well_formed in
      match p with
      | Some p' => Some (IncMetaNat inc a a' trans_a' p')
      | None => None
      end
  end.

Definition construct_absstack_stk_size_inc (inc: nat) (s: AbsStack): (absstack_stk_size_inc inc s (absstack_stack_size_inc inc s)) :=
  match s with
  | AbsStkTrue =>
      IncAbsStkTrue inc
  | AbsStkSize size =>
      IncAbsStkSize inc size
  end.
                                                      
Fixpoint construct_state_stk_size_inc (inc: nat) (P: AbsState): option (state_stk_size_inc inc P (absstate_stack_size_inc inc P)) :=
  match P with
  | BaseState s m =>
      let stack_size := construct_absstack_stk_size_inc inc s in
      let meta_stack := construct_meta_stk_size_inc inc m in
      match meta_stack with
      | Some H =>
          Some (IncBaseState inc s _ m _ stack_size H)
      | _ => None
      end
  | AbsAnd a1 a2 =>
      let s1 := construct_state_stk_size_inc inc a1 in
      let s2 := construct_state_stk_size_inc inc a2 in
      match s1, s2 with
      | Some H1, Some H2 =>
          Some (IncAbsAnd inc a1 a2 _ _ H1 H2)
      | _, _ => None
      end
  | AbsOr a1 a2 =>
      let s1 := construct_state_stk_size_inc inc a1 in
      let s2 := construct_state_stk_size_inc inc a2 in
      match s1, s2 with
      | Some H1, Some H2 =>
          Some (IncAbsOr inc a1 a2 _ _ H1 H2)
      | _, _ => None
      end
  end.


(* Lemma state_stk_size_inc_of_equal_things : *)
(*   forall (n: nat) (P Q: AbsState), *)
(*     P = absstate_stack_size_inc n Q -> *)
(*     state_stk_size_inc n Q (absstate_stack_size_inc n Q) -> *)
(*     state_stk_size_inc n Q P. *)
(* Proof. *)
(*   intros. rewrite H. eauto. *)
(* Defined. *)


Lemma aexp_stack_size_inc_det :
  forall (inc: nat) (a0 a a': aexp_stack),
    aexp_stk_size_inc_rel inc a0 a ->
    aexp_stk_size_inc_rel inc a0 a' ->
    a = a'.
Proof.
  intros.
  eapply aexp_stack_size_inc_adequacy_backward in H, H0.
  subst. reflexivity.
Defined.

Lemma bexp_stack_size_inc_det :
  forall (inc: nat) (b0 b b': bexp_stack),
    bexp_stk_size_inc_rel inc b0 b ->
    bexp_stk_size_inc_rel inc b0 b' ->
    b = b'.
Proof.
  intros.
  eapply bexp_stack_size_inc_adequacy_backward in H, H0. subst. reflexivity.
Defined.


Lemma meta_stack_size_inc_det :
  forall (inc: nat) (m0 m m': MetavarPred),
    meta_stk_size_inc inc m0 m ->
    meta_stk_size_inc inc m0 m' ->
    m = m'.
Proof.
  intros. eapply meta_stack_size_inc_adequacy_backward in H, H0.
  subst. reflexivity.
Defined.

Lemma state_stack_size_inc_adequacy_backward :
  forall (inc: nat) (P Q: AbsState),
    state_stk_size_inc inc P Q ->
    Q = absstate_stack_size_inc inc P.
Proof.
  intros inc P. revert inc. induction P; simpl; intros.
  - invs H. invs H3.
    + f_equal. eapply meta_stack_size_inc_adequacy_backward. assumption.
    + simpl. f_equal. eauto using meta_stack_size_inc_adequacy_backward.
  - invs H. f_equal; eauto.
  - invs H. f_equal; eauto.
Defined.

Lemma state_stk_size_inc_det :
  forall (inc: nat) (P: AbsState) (Q Q': AbsState),
    state_stk_size_inc inc P Q ->
    state_stk_size_inc inc P Q' ->
    Q = Q'.
Proof.
  intros.
  eapply state_stack_size_inc_adequacy_backward in H, H0.
  subst; eauto.
Defined.
