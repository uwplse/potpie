From Coq Require Import Arith Psatz Bool String List Nat Program.Equality ZArith.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Require Import DanTrick.StackLanguage DanTrick.StackLangTheorems DanTrick.StackFrame1 DanTrick.StackFrameMinHelpers DanTrick.StackFrameZ StackSemanticsMutInd.

Local Definition P_implies_nat_frame (a: aexp_stack) (fenv: fun_env_stk) (zframe: Z): Prop :=
  aexp_frame_rule a fenv (Z.to_nat zframe).

Local Definition P0_implies_nat_frame (args: list aexp_stack) (fenv: fun_env_stk) (zframe: Z): Prop :=
  args_frame_rule args fenv (Z.to_nat zframe).

Local Definition P1_implies_nat_frame (b: bexp_stack) (fenv: fun_env_stk) (zframe: Z): Prop :=
  bexp_frame_rule b fenv (Z.to_nat zframe).

Local Definition P2_implies_nat_frame (i: imp_stack) (fenv: fun_env_stk) (zframe zframe': Z): Prop :=
  imp_frame_rule i fenv (Z.to_nat zframe) (Z.to_nat zframe').

Theorem z_frame_implies_nat_frame :
  frame_z_rule_mut_ind_theorem P_implies_nat_frame P0_implies_nat_frame P1_implies_nat_frame P2_implies_nat_frame.
Proof.
  frame_z_rule_mutual_induction P P0 P1 P2 P_implies_nat_frame P0_implies_nat_frame P1_implies_nat_frame P2_implies_nat_frame; intros; try constructor; try assumption.
  - lia.
  - econstructor.
    + eassumption.
    + eassumption.
    + repeat rewrite Nat2Z.id in H0. assumption.
    + repeat rewrite Nat2Z.id in H1. assumption.
  - lia.
  - rewrite Z2Nat.inj_add; [ | lia .. ].
    simpl. unfold Pos.to_nat. unfold Pos.iter_op. constructor.
  - rewrite Z2Nat.inj_sub; [ | lia ].
    simpl. unfold Pos.to_nat. unfold Pos.iter_op. constructor.
    lia.
  - econstructor.
    + eassumption.
    + assumption.
Qed.

Section nat_conversion.
  Context (to_nat := Z.to_nat).
  Context (of_nat := Z.of_nat).
  
  Lemma imp_z_to_nat_frame :
    forall i fenv frame frame',
      imp_frame_z_rule i fenv frame frame' ->
      imp_frame_rule i fenv (to_nat frame) (to_nat frame').
  Proof using to_nat.
    intros. eapply z_frame_implies_nat_frame. assumption.
  Qed.

  Lemma aexp_z_to_nat_frame :
    forall a fenv frame,
      aexp_frame_z_rule a fenv frame ->
      aexp_frame_rule a fenv (to_nat frame).
  Proof using to_nat.
    intros. eapply z_frame_implies_nat_frame. assumption.
  Qed.

  Lemma bexp_z_to_nat_frame :
    forall b fenv frame,
      bexp_frame_z_rule b fenv frame ->
      bexp_frame_rule b fenv (to_nat frame).
  Proof using to_nat.
    intros. eapply z_frame_implies_nat_frame. assumption.
  Qed.
  
  Lemma args_z_to_nat_frame :
    forall args fenv frame,
      args_frame_z_rule args fenv frame ->
      args_frame_rule args fenv (to_nat frame).
  Proof using to_nat.
    intros. eapply z_frame_implies_nat_frame. assumption.
  Qed.

  Lemma imp_z_to_nat_frame' :
    forall i fenv frame frame' nframe nframe',
      imp_frame_z_rule i fenv frame frame' ->
      nframe = to_nat frame ->
      nframe' = to_nat frame' ->
      imp_frame_rule i fenv (nframe) (nframe').
  Proof using to_nat.
    intros. subst. eapply z_frame_implies_nat_frame. assumption.
  Qed.

  Lemma aexp_z_to_nat_frame' :
    forall a fenv frame nframe,
      aexp_frame_z_rule a fenv frame ->
      nframe = to_nat frame ->
      aexp_frame_rule a fenv (nframe).
  Proof using to_nat.
    intros. subst. eapply z_frame_implies_nat_frame. assumption.
  Qed.

  Lemma bexp_z_to_nat_frame' :
    forall b fenv frame nframe,
      bexp_frame_z_rule b fenv frame ->
      nframe = to_nat frame ->
      bexp_frame_rule b fenv (nframe).
  Proof using to_nat.
    intros. subst. eapply z_frame_implies_nat_frame. assumption.
  Qed.
  
  Lemma args_z_to_nat_frame' :
    forall args fenv frame nframe,
      args_frame_z_rule args fenv frame ->
      nframe = to_nat frame ->
      args_frame_rule args fenv (nframe).
  Proof using to_nat.
    intros. subst. eapply z_frame_implies_nat_frame. assumption.
  Qed.
End nat_conversion.


Local Definition P_implies_z_frame (a: aexp_stack) (fenv: fun_env_stk) (nframe: nat): Prop :=
  aexp_frame_z_rule a fenv (Z.of_nat nframe).

Local Definition P0_implies_z_frame (args: list aexp_stack) (fenv: fun_env_stk) (nframe: nat): Prop :=
  args_frame_z_rule args fenv (Z.of_nat nframe).

Local Definition P1_implies_z_frame (b: bexp_stack) (fenv: fun_env_stk) (nframe: nat): Prop :=
  bexp_frame_z_rule b fenv (Z.of_nat nframe).

Local Definition P2_implies_z_frame (i: imp_stack) (fenv: fun_env_stk) (nframe nframe': nat): Prop :=
  imp_frame_z_rule i fenv (Z.of_nat nframe) (Z.of_nat nframe').

Theorem nat_frame_implies_z_frame :
  frame_rule_mut_ind_theorem P_implies_z_frame P0_implies_z_frame P1_implies_z_frame P2_implies_z_frame.
Proof.
  frame_rule_mutual_induction P P0 P1 P2 P_implies_z_frame P0_implies_z_frame P1_implies_z_frame P2_implies_z_frame; intros; try constructor; try eapply Nat2Z.is_nonneg; try eassumption; try lia.
  - econstructor.
    + eapply Nat2Z.is_nonneg.
    + eassumption.
    + eassumption.
    + assumption.
    + assumption.
  - rewrite Nat2Z.inj_add.
    econstructor.
    eapply Nat2Z.is_nonneg.
  - rewrite Nat2Z.inj_sub.
    econstructor.
    lia. lia.
  - econstructor.
    + eapply Nat2Z.is_nonneg.
    + assert (0 <= Z.of_nat frame'). lia. eassumption.
    + eapply Nat2Z.is_nonneg.
    + eassumption.
    + eassumption.
Qed.

Section z_conversion.
  Context (of_nat := Z.of_nat).
  
  Lemma imp_nat_to_z_frame :
    forall i fenv (frame frame': nat),
      imp_frame_rule i fenv frame frame' ->
      imp_frame_z_rule i fenv (of_nat frame) (of_nat frame').
  Proof using of_nat.
    intros. eapply nat_frame_implies_z_frame. assumption.
  Qed.

  Lemma aexp_nat_to_z_frame :
    forall a fenv (frame: nat),
      aexp_frame_rule a fenv frame ->
      aexp_frame_z_rule a fenv (of_nat frame).
  Proof using of_nat.
    intros. eapply nat_frame_implies_z_frame. assumption.
  Qed.

  Lemma bexp_nat_to_z_frame :
    forall b fenv (frame: nat),
      bexp_frame_rule b fenv frame ->
      bexp_frame_z_rule b fenv (of_nat frame).
  Proof using of_nat.
    intros. eapply nat_frame_implies_z_frame. assumption.
  Qed.
+
  Lemma args_nat_to_z_frame :
    forall args fenv (frame: nat),
      args_frame_rule args fenv frame ->
      args_frame_z_rule args fenv (of_nat frame).
  Proof using of_nat.
    intros. eapply nat_frame_implies_z_frame. assumption.
  Qed.
End z_conversion.

Lemma aexp_frame_z_rule_implies_nonneg_frame :
  forall (a: aexp_stack) (fenv: fun_env_stk) (frame: Z),
    aexp_frame_z_rule a fenv frame ->
    0 <= frame.
Proof.
  destruct a; intros; invs H; try assumption.
  lia.
Qed.

Lemma bexp_frame_z_rule_implies_nonneg_frame :
  forall (b: bexp_stack) (fenv: fun_env_stk) (frame: Z),
    bexp_frame_z_rule b fenv frame ->
    0 <= frame.
Proof.
  induction b; intros; invs H; try assumption.
Qed.

Lemma args_frame_z_rule_implies_nonneg_frame :
  forall (args: list aexp_stack) (fenv: fun_env_stk) (frame: Z),
    args_frame_z_rule args fenv frame ->
    0 <= frame.
Proof.
  destruct args; intros; invs H; try assumption.
Qed.

Lemma imp_frame_z_rule_implies_nonneg_frame :
  forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': Z),
    imp_frame_z_rule i fenv frame frame' ->
    0 <= frame /\ 0 <= frame'.
Proof.
  destruct i; intros; invs H; split; try assumption; try lia.
Qed.

Local Definition P_min_frame (a: aexp_stack) (fenv: fun_env_stk) (frame: Z): Prop :=
  exists minframe,
    aexp_frame_z_rule a fenv minframe /\
      forall f,
        aexp_frame_z_rule a fenv f ->
        minframe <= f.
    
Local Definition P_frame_geq_preserved (a: aexp_stack) (fenv: fun_env_stk) (frame: Z): Prop :=
  forall stk1 stk2 n diff,
    0 <= diff ->
    aexp_stack_sem a fenv stk1 (stk2, n) ->
    Z.to_nat (frame + diff) = Datatypes.length stk1 ->
    Z.to_nat (frame + diff) = Datatypes.length stk2.

Local Definition P0_min_frame (args: list aexp_stack) (fenv: fun_env_stk) (frame: Z): Prop :=
  exists minframe,
    args_frame_z_rule args fenv minframe /\
      forall f,
        args_frame_z_rule args fenv f ->
        minframe <= f.

Local Definition P0_frame_geq_preserved (args: list aexp_stack) (fenv: fun_env_stk) (frame: Z): Prop :=
  forall stk1 stk2 vals diff,
    0 <= diff ->
    args_stack_sem args fenv stk1 (stk2, vals) ->
    Z.to_nat (frame + diff) = Datatypes.length stk1 ->
    Z.to_nat (frame + diff) = Datatypes.length stk2.

Local Definition P1_min_frame (b: bexp_stack) (fenv: fun_env_stk) (frame: Z) : Prop :=
  exists minframe,
    bexp_frame_z_rule b fenv minframe /\
      forall f,
        bexp_frame_z_rule b fenv f ->
        minframe <= f.

Local Definition P1_frame_geq_preserved (b: bexp_stack) (fenv: fun_env_stk) (frame: Z) : Prop :=
  forall stk1 stk2 v diff,
    0 <= diff ->
    bexp_stack_sem b fenv stk1 (stk2, v) ->
    Z.to_nat (frame + diff) = Datatypes.length stk1 ->
    Z.to_nat (frame + diff) = Datatypes.length stk2.

Local Definition P2_frame_geq_preserved (i: imp_stack) (fenv: fun_env_stk) (frame frame': Z) : Prop :=
  forall stk1 stk2 diff,
    0 <= diff ->
    imp_stack_sem i fenv stk1 stk2 ->
    Z.to_nat (frame + diff) = Datatypes.length stk1 ->
    Z.to_nat (frame' + diff) =  Datatypes.length stk2.

Local Definition P2_min_frame (i: imp_stack) (fenv: fun_env_stk) (frame frame': Z): Prop :=
  exists minframe,
    imp_frame_z_rule i fenv minframe ((minframe + frame') - frame) /\
      forall f f',
        imp_frame_z_rule i fenv f f' ->
        minframe <= f.

Lemma aexp_zframe_expansion :
  forall a fenv frame frame',
    aexp_frame_z_rule a fenv frame ->
    frame <= frame' ->
    aexp_frame_z_rule a fenv frame'.
Proof.
  intros.
  pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
  assert (0 <= frame') by lia.
  eapply Z_of_nat_complete in H2. destruct H2. rewrite H2.
  eapply nat_frame_implies_z_frame. eapply aexp_frame_expansion.
  eapply z_frame_implies_nat_frame. eassumption. lia.
Qed.

Lemma bexp_zframe_expansion :
  forall b fenv frame frame',
    bexp_frame_z_rule b fenv frame ->
    frame <= frame' ->
    bexp_frame_z_rule b fenv frame'.
Proof.
  intros.
  pose proof (bexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
  assert (0 <= frame') by lia.
  eapply Z_of_nat_complete in H2. destruct H2. rewrite H2.
  eapply nat_frame_implies_z_frame. eapply bexp_frame_expansion.
  eapply z_frame_implies_nat_frame. eassumption. lia.
Qed.

Lemma args_zframe_expansion :
  forall args fenv frame frame',
    args_frame_z_rule args fenv frame ->
    frame <= frame' ->
    args_frame_z_rule args fenv frame'.
Proof.
  intros.
  pose proof (args_frame_z_rule_implies_nonneg_frame _ _ _ H).
  assert (0 <= frame') by lia.
  eapply Z_of_nat_complete in H2. destruct H2. rewrite H2.
  eapply nat_frame_implies_z_frame. eapply args_frame_expansion.
  eapply z_frame_implies_nat_frame. eassumption. lia.
Qed.

Lemma imp_zframe_expansion :
  forall i fenv frame frame' frame'',
    imp_frame_z_rule i fenv frame frame' ->
    frame <= frame'' ->
    imp_frame_z_rule i fenv frame'' (frame'' + frame' - frame).
Proof.
  intros.
  pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H).
  destruct H1.
  assert (0 <= frame'') by lia.
  eapply Z_of_nat_complete in H1, H2, H3. destruct H1, H2, H3. rewrite H1, H2, H3.
  rewrite <- Nat2Z.inj_add.
  rewrite <- Nat2Z.inj_sub.
  eapply nat_frame_implies_z_frame. eapply imp_frame_expansion.
  assert (Z.to_nat frame = x) by lia.
  assert (Z.to_nat frame' = x0) by lia.
  rewrite <- H4, <- H5.
  eapply z_frame_implies_nat_frame. eassumption. lia. lia.
Qed.

Section frames_same.
  Context (of_nat := Z.of_nat).
  Context (to_nat := Z.to_nat).
  Context (Dlength := Datatypes.length).
  Context (Zlength := fun (stk: list nat) => of_nat (Dlength _ stk)).

  Ltac unfold_consts :=
    try unfold Zlength in *;
    try unfold Dlength in *;
    try unfold of_nat in *;
    try unfold to_nat in *.

  Lemma aexp_zframe_implies_pure :
    forall (a: aexp_stack) (fenv: fun_env_stk) (frame: Z) (stk stk': stack) (v: nat),
      aexp_frame_z_rule a fenv frame ->
      aexp_stack_sem a fenv stk (stk', v) ->
      stk = stk'.
  Proof.
    pose proof (aexp_frame_implies_pure) as H.
    intros.
    eapply aexp_z_to_nat_frame in H0. eapply H in H0. eassumption. eassumption.
  Qed.


  Lemma bexp_zframe_implies_pure :
    forall (b: bexp_stack) (fenv: fun_env_stk) (frame: Z) (stk stk': stack) (v: bool),
      bexp_frame_z_rule b fenv frame ->
      bexp_stack_sem b fenv stk (stk', v) ->
      stk = stk'.
  Proof.
    pose proof (bexp_frame_implies_pure) as H.
    intros.
    eapply bexp_z_to_nat_frame in H0. eapply H in H0. eassumption. eassumption.
  Qed.

  Lemma args_zframe_implies_pure :
    forall (args: list aexp_stack) (fenv: fun_env_stk) (frame: Z) (stk stk': stack) (vals: list nat),
      args_frame_z_rule args fenv frame ->
      args_stack_sem args fenv stk (stk', vals) ->
      stk = stk'.
  Proof.
    pose proof (args_frame_implies_pure).
    intros.
    eapply args_z_to_nat_frame in H0. eapply H in H0. eassumption. eassumption.
  Qed.

   Lemma Z_add_sub :
    forall z1 z2,
      z1 + z2 - z2 = z1.
  Proof.
    intros. lia.
  Qed.

  Lemma Z_add_add_sub :
    forall a b c,
      a + (b + c) - b = a + c.
  Proof.
    lia.
  Qed.

  Lemma Z_add_sub_sub :
    forall a b c,
      a + (b - c) - b = a - c.
  Proof.
    lia.
  Qed.

  Lemma Z_sub_sub_add :
    forall a b c,
      a - (b - c) + b = a + c.
  Proof.
    lia.
  Qed.

  Lemma stacks_zframes_same :
    forall i fenv stk stk',
    forall (Himp: imp_stack_sem i fenv stk stk'),
    forall  frame frame',
    forall (Hframe: imp_frame_z_rule i fenv frame frame'),
      frame' - frame = Zlength stk' - Zlength stk.
  Proof.
    intros i fenv stk stk' Himp.
    induction Himp; intros; unfold_consts.
    - invs Hframe. lia.
    - invs Hframe. eapply stack_mutated_at_index_preserves_length in H2.
      eapply aexp_zframe_implies_pure in H1. subst. lia.
      eassumption.
    - invs Hframe. simpl. destruct (-Z.of_nat (Datatypes.length stk)) eqn:?.
      + rewrite Zminus_plus.
        lia.
      + lia.
      + rewrite Zminus_plus. assert (Z.of_nat (Datatypes.length stk) = Z.pos p). lia.
        assert (Datatypes.length stk = Z.to_nat (Z.pos p)) by lia. rewrite H1. simpl.
        rewrite Pos2SuccNat.id_succ.
        assert (Pos.succ p > p)%positive by lia.
        rewrite Field_theory.Z_pos_sub_gt.
        rewrite <- Pos2SuccNat.id_succ.
        rewrite Pos.of_nat_succ.
        rewrite <- Z.pos_sub_gt.
        rewrite <- Pos.sub_diag with (p := p).
        rewrite <- Pos2Z.add_pos_neg.
        rewrite <- Pos.of_nat_succ.
        rewrite Pos2SuccNat.id_succ. rewrite Pos2Z.inj_succ.
        lia. lia. assumption.
    - invs Hframe. simpl. lia.
    - invs Hframe.
      eapply IHHimp1 in H4. eapply IHHimp2 in H8.
      remember (Z.of_nat (Datatypes.length stk')) as lstk'.
      remember (Z.of_nat (Datatypes.length stk'')) as lstk''.
      remember (Z.of_nat (Datatypes.length stk)) as lstk.
      pose proof (Z_le_gt_dec frame zframe').
      pose proof (Z_le_gt_dec zframe' frame').
      destruct H, H0; lia.
    - invs Hframe. assert (stk = stk') by (eapply bexp_zframe_implies_pure; eassumption); subst stk. 
      eapply IHHimp. eassumption.
    - invs Hframe. assert (stk = stk') by (eapply bexp_zframe_implies_pure; eassumption); subst stk. 
      eapply IHHimp. eassumption.
    - invs Hframe.  assert (stk = stk') by (eapply bexp_zframe_implies_pure; eassumption); subst stk.  lia.
    - invs Hframe. assert (stk = stk1) by (eapply bexp_zframe_implies_pure; eassumption); subst stk.
      eapply IHHimp1 in H7. eapply IHHimp2 in Hframe. lia.
  Qed.

  Lemma zframes_same :
    forall i fenv,
    forall  frame frame' f f',
    forall (Hframe: imp_frame_z_rule i fenv frame frame'),
    forall (Hf: imp_frame_z_rule i fenv f f'),
      frame' - frame = f' - f.
  Proof.
    intros.
    pose proof (frame_relative).
    pose proof (NONNEG := imp_frame_z_rule_implies_nonneg_frame).
    
    unfold int_diff_nats in H.
    pose proof (imp_z_to_nat_frame).
    pose proof (H0 i fenv frame frame' Hframe).
    specialize (H0 i fenv f f' Hf).
    pose proof (NONNEG i fenv frame frame' Hframe).
    specialize (NONNEG i fenv f f' Hf).
    destruct NONNEG, H2.
    remember (Z.to_nat f') as zf'.
    remember (Z.to_nat f) as zf.
    remember (Z.to_nat frame) as zframe.
    remember (Z.to_nat frame') as zframe'.
    specialize (H i fenv zframe zframe' H1 zf zf' H0).
    rewrite Heqzf', Heqzf, Heqzframe, Heqzframe' in H.
    rewrite Z2Nat.id in H. rewrite Z2Nat.id in H. rewrite Z2Nat.id in H. rewrite Z2Nat.id in H.
    symmetry. assumption. assumption. assumption. assumption. assumption.
  Qed.
    
End frames_same.

Lemma imp_zframe_switch :
  forall i fenv frame frame' f f',
    imp_frame_z_rule i fenv frame frame' ->
    imp_frame_z_rule i fenv f f' ->
    forall frame'',
      imp_frame_z_rule i fenv frame'' (frame'' + frame' - frame) ->
      imp_frame_z_rule i fenv frame'' (frame'' + f' - f).
Proof.
  intros.
  pose proof (zframes_same). specialize (H2 i fenv frame frame' f f' H H0).
  rewrite <- Z.add_sub_assoc. rewrite <- H2. rewrite Z.add_sub_assoc. assumption.
Qed.

Lemma imp_zframe_deterministic1 :
  forall i fenv frame frame' frame'',
    imp_frame_z_rule i fenv frame frame' ->
    imp_frame_z_rule i fenv frame'' frame' ->
    frame = frame''.
Proof.
  intros. 
  destruct (imp_frame_z_rule_implies_nonneg_frame i fenv frame frame' H).
  destruct (imp_frame_z_rule_implies_nonneg_frame i fenv frame'' frame' H0).
  rewrite <- (Z2Nat.id frame H1).
  rewrite <- (Z2Nat.id frame'' H3).
  apply imp_z_to_nat_frame in H. apply imp_z_to_nat_frame in H0.
  f_equal. eapply frame_deterministic'; eauto.
Qed.

Lemma imp_zframe_deterministic2 :
  forall i fenv frame frame' frame'',
    imp_frame_z_rule i fenv frame frame' ->
    imp_frame_z_rule i fenv frame frame'' ->
    frame' = frame''.
Proof.
  intros. 
  destruct (imp_frame_z_rule_implies_nonneg_frame i fenv frame frame' H).
  destruct (imp_frame_z_rule_implies_nonneg_frame i fenv frame frame'' H0).
  rewrite <- (Z2Nat.id frame' H2).
  rewrite <- (Z2Nat.id frame'' H4).
  apply imp_z_to_nat_frame in H. apply imp_z_to_nat_frame in H0.
  f_equal. eapply frame_deterministic; eauto.
Qed.

Lemma frame_cant_decrease_too_much :
  forall i fenv frame frame',
    imp_frame_z_rule i fenv frame frame' ->
    frame' <= frame ->
    forall f f',
      imp_frame_z_rule i fenv f f' ->
      Z.abs (frame - frame') <= f.
Proof.
  intros.
  pose proof (Z_le_gt_dec (Z.abs (frame - frame')) f).
  destruct H2; [ auto | ].
  assert (0 <= frame - frame') by lia.
  rewrite Z.abs_eq; [ | assumption ].
  pose proof (frame_relative''' _ _ _ _
                                (imp_z_to_nat_frame _ _ _ _ H)
                                _ _
                                (imp_z_to_nat_frame _ _ _ _ H1)).
  pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H).
  pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H1).
  destruct H4. destruct H5.
  destruct H3; destruct H3.
  - assert (frame' >= frame) by lia.
    assert (frame' = frame) by lia. subst. lia.
  - assert (Z.of_nat (Z.to_nat f' + Z.to_nat frame - Z.to_nat frame') = Z.of_nat (Z.to_nat f)) by (f_equal; assumption).
    assert (f' + frame - frame' = f) by lia.
    rewrite Z.abs_eq in g.
    assert (frame - frame' <= f) by lia.
    congruence.
    assumption.
Qed.

Lemma min_zframe :
  frame_z_rule_mut_ind_theorem P_min_frame P0_min_frame P1_min_frame P2_min_frame.
Proof.
  frame_z_rule_mutual_induction P P0 P1 P2 P_min_frame P0_min_frame P1_min_frame P2_min_frame; intros.
  - exists 0. split; intros.
    + constructor. auto with zarith.
    + invs H. auto.
  - exists (Z.of_nat k).
    split; intros.
    + constructor. assumption. reflexivity.
    + invs H. assumption.
  - destruct H, H0. destruct H, H0.
    pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H0).
    exists (Z.max x x0).
    split; intros.
    + constructor.
      lia.
      assert (0 <= Z.max x x0) by lia.
      eapply Z_of_nat_complete in H5. destruct H5. rewrite H5.
      eapply nat_frame_implies_z_frame. eapply aexp_frame_expansion.
      eapply z_frame_implies_nat_frame. eassumption. lia.
      eapply aexp_zframe_expansion. eassumption. lia.
    + invs H5. eapply H1 in H9. eapply H2 in H12. lia.
  - destruct H, H0. destruct H, H0.
    pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H0).
    exists (Z.max x x0).
    split; intros.
    + constructor.
      lia.
      assert (0 <= Z.max x x0) by lia.
      eapply Z_of_nat_complete in H5. destruct H5. rewrite H5.
      eapply nat_frame_implies_z_frame. eapply aexp_frame_expansion.
      eapply z_frame_implies_nat_frame. eassumption. lia.
      eapply aexp_zframe_expansion. eassumption. lia.
    + invs H5. eapply H1 in H9. eapply H2 in H12. lia.
  - destruct H, H0, H1. destruct H, H0, H1. exists x.
    pose proof (args_frame_z_rule_implies_nonneg_frame _ _ _ H).
    split; intros.
    + econstructor.
      * assumption.
      * assumption.
      * eassumption.
      * assumption.
      * assumption.
    + invs H6. eapply H2 in H10. assumption.
  - exists 0. split; [constructor | intros]; auto with zarith.
    invs H. auto.
  - destruct H, H0. destruct H, H0.
    pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    pose proof (args_frame_z_rule_implies_nonneg_frame _ _ _ H0).
    exists (Z.max x x0).
    split.
    + constructor. lia. eapply aexp_zframe_expansion.  eapply H. lia.
      eapply args_zframe_expansion. eapply H0. lia.
    + intros. invs H5. eapply H1 in H9. eapply H2 in H12. lia.
  - exists 0. split; intros. constructor. lia. invs H. auto.
  - exists 0. split; intros.
    constructor. lia. invs H. auto.
  - destruct H. destruct H.
    pose proof (bexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    exists x. split; intros.
    + constructor. assumption. assumption.
    + invs H2. apply H0 in H5. assumption.
  - destruct H, H0. destruct H, H0. pose proof (bexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    pose proof (bexp_frame_z_rule_implies_nonneg_frame _ _ _ H0).
    exists (Z.max x x0).
    split; intros.
    + econstructor.
      * lia.
      * eapply bexp_zframe_expansion. eapply H. lia.
      * eapply bexp_zframe_expansion. eapply H0. lia.
    + invs H5. eapply H1 in H9. eapply H2 in H12. lia.
  - destruct H, H0. destruct H, H0. pose proof (bexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    pose proof (bexp_frame_z_rule_implies_nonneg_frame _ _ _ H0).
    exists (Z.max x x0).
    split; intros.
    + econstructor.
      * lia.
      * eapply bexp_zframe_expansion. eapply H. lia.
      * eapply bexp_zframe_expansion. eapply H0. lia.
    + invs H5. eapply H1 in H9. eapply H2 in H12. lia.
  - destruct H, H0. destruct H, H0.
    pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H0).
    exists (Z.max x x0).
    split; intros.
    + constructor.
      lia.
      assert (0 <= Z.max x x0) by lia.
      eapply Z_of_nat_complete in H5. destruct H5. rewrite H5.
      eapply nat_frame_implies_z_frame. eapply aexp_frame_expansion.
      eapply z_frame_implies_nat_frame. eassumption. lia.
      eapply aexp_zframe_expansion. eassumption. lia.
    + invs H5. eapply H1 in H9. eapply H2 in H12. lia.
  - destruct H, H0. destruct H, H0.
    pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H0).
    exists (Z.max x x0).
    split; intros.
    + constructor.
      lia.
      assert (0 <= Z.max x x0) by lia.
      eapply Z_of_nat_complete in H5. destruct H5. rewrite H5.
      eapply nat_frame_implies_z_frame. eapply aexp_frame_expansion.
      eapply z_frame_implies_nat_frame. eassumption. lia.
      eapply aexp_zframe_expansion. eassumption. lia.
    + invs H5. eapply H1 in H9. eapply H2 in H12. lia.
  - exists 0. split; intros.
    rewrite <- Z.add_sub_assoc.
    rewrite Z.sub_diag. simpl. constructor. lia.
    invs H. assumption.
  - destruct H. destruct H.
    pose proof (aexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    exists (Z.max x (Z.of_nat k)).
    split.
    + rewrite Z.add_simpl_r. econstructor; try assumption.
      * lia.
      * eapply aexp_zframe_expansion.
        eassumption. lia.
    + intros.
      invs H2. eapply H0 in H10. lia.
  - exists 0. simpl. rewrite Z.add_simpl_l. split; intros.
    + constructor. auto with zarith.
    + invs H. auto.
  - exists 1. rewrite Zplus_minus. rewrite Z.sub_diag. split; intros.
    + constructor. lia.
    + invs H. lia.
  - destruct H, H0. destruct H, H0.
    pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H).
    pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H0).
    destruct H3, H4.
    pose proof (Z_le_gt_dec zframe zframe'). destruct H7.
    + pose proof (Z_le_gt_dec (x + zframe' - zframe) x0). destruct H7.
      -- exists (x0 + zframe - zframe').
         split.
         ++ econstructor.
            ** lia.
            ** eapply H4.
            ** lia.
            ** assert (x0 = x0 + zframe - zframe' + zframe' - zframe) by lia.
               remember (x0 + zframe - zframe') as blah.
               rewrite H7. subst blah.
               eapply imp_zframe_switch.
               eapply H. eassumption.
               eapply imp_zframe_expansion. assumption. lia.
            ** assert (x0 + zframe - zframe' + zframe'' - zframe = x0 + zframe'' - zframe'). lia. rewrite H7. assumption.
         ++ intros. invs H7.
            assert (x0 + zframe - zframe' <= x0) by lia.
            assert (x <= x0) by lia.
            pose proof (H2 _ _ H17).
            pose proof (H1 _ _ H13).
            pose proof (imp_zframe_expansion). specialize (H16 _ _ _ _ f H H15).
            assert (f + (x + zframe' - zframe) - x = f + zframe' - zframe) by lia.
            rewrite H18 in H16. clear H18.
            assert (zframe'0 = f + zframe' - zframe).
            eapply imp_zframe_deterministic2. eassumption. assumption. subst zframe'0. lia.
      -- exists x. split.
         ++ econstructor.
            ** assumption.
            ** eapply H5.
            ** pose proof (H1 _ _ i). lia.
            ** assumption.
            ** assert (x + zframe'' - zframe = x + zframe' - zframe + zframe'' - zframe') by lia.
               rewrite H7.
               eapply imp_zframe_switch.
               eapply H0. eassumption. eapply imp_zframe_expansion.
               assumption. lia.
         ++ intros. invs H7. eapply H1. eassumption.
    + pose proof (Z_le_gt_dec x x0).
      destruct H7.
      * exists (x0 + zframe - zframe').
         split.
         ++ econstructor.
            ** lia.
            ** eapply H4.
            ** lia.
            ** assert (x0 = x0 + zframe - zframe' + zframe' - zframe) by lia.
               remember (x0 + zframe - zframe') as blah.
               rewrite H7. subst blah.
               eapply imp_zframe_switch.
               eapply H. eassumption.
               eapply imp_zframe_expansion. assumption. lia.
            ** assert (x0 + zframe - zframe' + zframe'' - zframe = x0 + zframe'' - zframe'). lia. rewrite H7. assumption.
         ++ intros. invs H7.
            pose proof (imp_zframe_expansion).
            pose proof (H1 _ _ H13).
            specialize (H8 _ _ _ _ f H H9).
            assert (f + (x + zframe' - zframe) - x = f + zframe' - zframe) by lia.
            rewrite H14 in H8.
            
            assert (zframe'0 = f + zframe' - zframe).
            eapply imp_zframe_deterministic2. eassumption. assumption. subst zframe'0.
            specialize (H2 _ _ H17). lia.
      * pose proof (Z_le_gt_dec (x0 + zframe - zframe') x).
        destruct H7.
        -- exists x. split; intros.
           ++ econstructor.
              ** assumption.
              ** eapply H5.
              ** lia.
              ** assumption.
              ** assert (x + zframe'' - zframe = x + zframe' - zframe + zframe'' - zframe') by lia.
                 rewrite H7. eapply imp_zframe_switch. eapply H0. eassumption.
                 eapply imp_zframe_expansion. assumption. lia.
           ++ invs H7. eapply H1. eassumption.
        -- exists (x0 + zframe - zframe').
           split; intros.
           ++ econstructor.
              ** lia.
              ** eapply H4.
              ** lia.
              ** assert (x0 = x0 + zframe - zframe' + zframe' - zframe) by lia.
                 remember (x0 + zframe - zframe') as blah. rewrite H7. subst blah.
                 eapply imp_zframe_switch. eapply H. assumption. eapply imp_zframe_expansion.
                 assumption. lia.
              ** assert (x0 + zframe - zframe' + zframe'' - zframe = x0 + zframe'' - zframe') by lia.
                 rewrite H7. assumption.
           ++ intros. invs H7.
              pose proof (imp_zframe_expansion).
              pose proof (H1 _ _ H13).
              assert (x0 + zframe - zframe' < x + zframe - zframe') by lia.
              
              specialize (H8 _ _ _ _ f H H9).
              assert (f + (x + zframe' - zframe) - x = f + zframe' - zframe) by lia.
              rewrite H15 in H8.
            
              assert (zframe'0 = f + zframe' - zframe).
              eapply imp_zframe_deterministic2. eassumption. assumption. subst zframe'0.
              specialize (H2 _ _ H17). lia.
  - destruct H, H0, H1. destruct H, H0, H1. exists (Z.max (Z.max x x0) x1).
    pose proof (bexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H0).
    pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H1).
    destruct H6, H7.
    split; intros.
    + econstructor; try lia.
      eapply bexp_zframe_expansion.
      eapply H. lia.
      eapply imp_zframe_switch. eapply H0. assumption. eapply imp_zframe_expansion. assumption. lia.
      eapply imp_zframe_switch. eapply H1. assumption. eapply imp_zframe_expansion. assumption. lia.
    + invs H10. eapply H2 in H16. eapply H3 in H20. eapply H4 in H21. lia.
  - destruct H, H0. destruct H, H0.
    exists (Z.max x x0).
    pose proof (bexp_frame_z_rule_implies_nonneg_frame _ _ _ H).
    pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H0). destruct H4.
    split.
    + rewrite <- Z.add_sub_assoc. rewrite Z.sub_diag. rewrite Z.add_0_r. econstructor.
      * lia.
      * eapply bexp_zframe_expansion. eapply H. lia.
      * rewrite <- Z.add_0_r. rewrite <- (Z.sub_diag x0). rewrite Z.add_sub_assoc. eapply imp_zframe_expansion.
        rewrite Z.add_simpl_r in H0. assumption. lia.
    + intros.
      invs H6. specialize (H1 _ H10).
      specialize (H2 _ _ H14). lia.
Qed.

Lemma aexp_min_zframe :
  (forall (a : aexp_stack) (fenv : fun_env_stk) (zframe : Z),
   aexp_frame_z_rule a fenv zframe ->
   exists minframe : Z,
     aexp_frame_z_rule a fenv minframe /\
       (forall f : Z, aexp_frame_z_rule a fenv f -> minframe <= f)).
Proof.
  destruct min_zframe. intuition.
Qed.

Lemma args_min_zframe :
   (forall (args : list aexp_stack) (fenv : fun_env_stk) (zframe : Z),
   args_frame_z_rule args fenv zframe ->
   exists minframe : Z,
     args_frame_z_rule args fenv minframe /\
       (forall f : Z, args_frame_z_rule args fenv f -> minframe <= f)).
Proof.
  destruct min_zframe. intuition.
Qed.

Lemma bexp_min_zframe :
  (forall (b : bexp_stack) (fenv : fun_env_stk) (zframe : Z),
   bexp_frame_z_rule b fenv zframe ->
   exists minframe : Z,
     bexp_frame_z_rule b fenv minframe /\
       (forall f : Z, bexp_frame_z_rule b fenv f -> minframe <= f)).
Proof.
  destruct min_zframe. intuition.
Qed.

Lemma imp_min_zframe :
  (forall (i : imp_stack) (fenv : fun_env_stk) (zframe zframe' : Z),
   imp_frame_z_rule i fenv zframe zframe' ->
   exists minframe : Z,
     imp_frame_z_rule i fenv minframe (minframe + zframe' - zframe) /\
       (forall f f' : Z, imp_frame_z_rule i fenv f f' -> minframe <= f)).
Proof.
    destruct min_zframe. intuition.
Qed.


Section Z_stk_frame.
  Context (of_nat := Z.of_nat).
  Context (to_nat := Z.to_nat).
  Context (Dlength := Datatypes.length).
  Context (Zlength := fun (stk: list nat) => of_nat (Dlength _ stk)).

  Ltac unfold_consts :=
    try unfold Zlength in *;
    try unfold Dlength in *;
    try unfold of_nat in *;
    try unfold to_nat in *.

  Lemma skip_zminframe_is_zero :
    forall fenv minframe,
    (imp_frame_z_rule Skip_Stk fenv minframe minframe /\
       (forall f f' : Z,
           imp_frame_z_rule Skip_Stk fenv f f' -> minframe <= f)) ->
    minframe = 0.
  Proof.
    intros. destruct H.
    specialize (H0 0 0).
    invs H.
    assert (imp_frame_z_rule Skip_Stk fenv 0 0).
    econstructor. auto with zarith.
    apply H0 in H2. lia.
  Qed.

  Lemma push_zminframe_is_zero :
    forall fenv minframe,
    (imp_frame_z_rule Push_Stk fenv minframe (minframe + 1) /\
       (forall f f' : Z,
           imp_frame_z_rule Push_Stk fenv f f' -> minframe <= f)) ->
    minframe = 0.
  Proof.
    intros. destruct H.
    specialize (H0 0 1). invs H.
    assert (imp_frame_z_rule Push_Stk fenv 0 1).
    constructor. lia.
    apply H0 in H2. lia.
  Qed.

  Lemma pop_zminframe_is_one :
    forall fenv minframe,
    (imp_frame_z_rule Pop_Stk fenv minframe (minframe - 1) /\
       (forall f f' : Z,
           imp_frame_z_rule Pop_Stk fenv f f' -> minframe <= f)) ->
    minframe = 1.
  Proof.
    intros. destruct H.
    specialize (H0 1 0). invs H.
    assert (imp_frame_z_rule Pop_Stk fenv 1 0).
    constructor. lia.
    apply H0 in H2. lia.
  Qed.

  Lemma timtowdi :
    forall fenv i frame frame' f f',
      imp_frame_z_rule i fenv frame frame' ->
      imp_frame_z_rule i fenv f f' ->
      imp_frame_z_rule i fenv frame (frame + f' - f).
  Proof.
    intros. pose proof (imp_zframe_switch).
    specialize (H1 _ _ _ _ _ _ H H0).
    assert (frame + frame' - frame = frame') by lia.
    rewrite <- H2 in H. specialize (H1 _ H). assumption.
  Qed.

  Lemma timtowdi' :
    forall fenv i frame frame' f f',
      imp_frame_z_rule i fenv frame frame' ->
      imp_frame_z_rule i fenv f f' ->
      frame' = frame + f' - f.
  Proof.
    intros. eapply imp_zframe_deterministic2. eassumption.
    eapply timtowdi. eassumption. assumption.
  Qed.

  Lemma timtowdi'' :
    forall fenv i frame frame' f f',
      imp_frame_z_rule i fenv frame frame' ->
      frame <= f ->
      f' = f + frame' - frame ->
      imp_frame_z_rule i fenv f f'.
  Proof.
    intros.
    pose proof (imp_zframe_expansion).
    specialize (H2 _ _ _ _ f H). subst. apply H2 in H0. assumption.
  Qed.
    

  Lemma seq_zminframe_leq_is_max :
    forall fenv i1 i2 frame frame' frame'',
      imp_frame_z_rule (Seq_Stk i1 i2) fenv frame frame'' ->
      imp_frame_z_rule i1 fenv frame frame' ->
      imp_frame_z_rule i2 fenv frame' frame'' ->
      forall minframe1 minframe2,
        (imp_frame_z_rule i1 fenv minframe1 (minframe1 + frame' - frame) /\
           forall f f',
             imp_frame_z_rule i1 fenv f f' -> minframe1 <= f) ->
        (imp_frame_z_rule i2 fenv minframe2 (minframe2 + frame'' - frame') /\
           forall f f',
             imp_frame_z_rule i2 fenv f f' -> minframe2 <= f) ->
        forall minframe,
          (imp_frame_z_rule (Seq_Stk i1 i2) fenv minframe (minframe + frame'' - frame) /\
             (forall f f' : Z,
                 imp_frame_z_rule (Seq_Stk i1 i2) fenv f f' -> minframe <= f)) ->
          frame <= frame' ->
          minframe = Z.max minframe1 (minframe2 + frame - frame').
  Proof.
    intros.
    destruct H4. destruct H2, H3.
    invs H4.
    pose proof (timtowdi'). specialize (H9 _ _ _ _ _ _ H14 H0).
    subst zframe'.
    pose proof (Z.max_spec).
    pose proof (imp_frame_z_rule_implies_nonneg_frame).
    pose proof (H10 _ _ _ _ H2).
    specialize (H10 _ _ _ _ H3).
    specialize (H9 minframe1 (minframe2 + frame - frame')).
    destruct H9.
    - destruct H9.
      pose proof (imp_zframe_expansion).
      specialize (H17 _ _ _ _ (minframe2 + frame - frame') H2).
      assert (minframe1 <= minframe2 + frame - frame') by lia.
      specialize (H17 H19). clear H19.
      assert (minframe2 + frame - frame' + (minframe1 + frame' - frame) -
                minframe1 = minframe2) by lia. rewrite H19 in H17. clear H19.
      assert (imp_frame_z_rule (Seq_Stk i1 i2) fenv (minframe2 + frame - frame') (minframe2 + frame - frame' + frame'' - frame)).
      econstructor. lia. destruct H10. eapply l. destruct H10. destruct H15.
      pose proof (H8 _ _ H18). pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H18). destruct H22.
      assert (minframe2 + frame - frame' + frame'' - frame = minframe2 + frame'' - frame') by lia. rewrite H24. pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H1). destruct H25.
      pose proof (Z_le_gt_dec frame' frame''). destruct H27.
      +  lia.
      + assert (frame'' <= frame') by lia.
        pose proof (frame_cant_decrease_too_much _ _ _ _ H1 H27 _ _ H3). lia.
      + destruct H10, H15. assumption.
      + assert (minframe2 + frame - frame' + frame'' - frame = minframe2 + frame'' - frame') by lia.
        rewrite H19. eapply imp_zframe_switch. eapply H3. assumption. assert ((minframe2 + (minframe2 + frame'' - frame') - minframe2) = minframe2 + frame'' - frame') by lia. rewrite H20. assumption.
      + pose proof (H6 _ _ H19). assert (minframe <= minframe2) by lia.
        assert (minframe2 + frame - frame' <= minframe2) by lia.
        pose proof (H8 _ _ H18).
        assert (minframe2 + frame - frame' <= minframe) by lia.
        assert (minframe = minframe2 + frame - frame') by lia. lia.
    - destruct H10. destruct H15. destruct H9.
      assert (minframe2 <= minframe1 + frame' - frame) by lia.
      assert (imp_frame_z_rule (Seq_Stk i1 i2) fenv minframe1 (minframe1 + frame'' - frame)).
      econstructor. assumption.
      eapply H17.
      + pose proof (Z_le_gt_dec frame frame''). destruct H21. lia.
        pose proof (frame_cant_decrease_too_much _ _ _ _ H).
        assert (frame'' <= frame) by lia.
        specialize (H21 H22). specialize (H21 _ _ H4).
        pose proof (H8 _ _ H18).
        assert (minframe2 + frame - frame' <= minframe). lia.
        pose proof (Z_le_gt_dec frame' frame''). destruct H25.
        * lia.
        * rewrite Z.abs_eq in H21; [ | lia ].
          assert (frame <= minframe + frame'') by lia.
          lia.
      + assumption.
      + assert (minframe1 + frame'' - frame = minframe1 + frame' - frame + frame'' - frame') by lia. rewrite H21. clear H21. eapply imp_zframe_switch. eapply H3. assumption. eapply imp_zframe_expansion. assumption. lia.
      + pose proof (H6 _ _ H21). pose proof (H7 _ _ H14). lia.
  Qed.

  Lemma seq_zminframe_gt_is_max :
    forall fenv i1 i2 frame frame' frame'',
      imp_frame_z_rule (Seq_Stk i1 i2) fenv frame frame'' ->
      imp_frame_z_rule i1 fenv frame frame' ->
      imp_frame_z_rule i2 fenv frame' frame'' ->
      forall minframe1 minframe2,
        (imp_frame_z_rule i1 fenv minframe1 (minframe1 + frame' - frame) /\
           forall f f',
             imp_frame_z_rule i1 fenv f f' -> minframe1 <= f) ->
        (imp_frame_z_rule i2 fenv minframe2 (minframe2 + frame'' - frame') /\
           forall f f',
             imp_frame_z_rule i2 fenv f f' -> minframe2 <= f) ->
        forall minframe,
          (imp_frame_z_rule (Seq_Stk i1 i2) fenv minframe (minframe + frame'' - frame) /\
             (forall f f' : Z,
                 imp_frame_z_rule (Seq_Stk i1 i2) fenv f f' -> minframe <= f)) ->
          frame > frame' ->
          minframe = Z.max minframe1 (minframe2 + frame - frame').
  Proof.
    intros.
    destruct H4. destruct H2, H3.
    invs H4.
    pose proof (timtowdi'). specialize (H9 _ _ _ _ _ _ H14 H0).
    subst zframe'.
    pose proof (Z.max_spec).
    pose proof (imp_frame_z_rule_implies_nonneg_frame).
    pose proof (H10 _ _ _ _ H2).
    specialize (H10 _ _ _ _ H3).
    specialize (H9 minframe1 (minframe2 + frame - frame')).
    pose proof (H7 _ _ H14).
    pose proof (H8 _ _ H18).
    destruct H10; destruct H15; destruct H9; destruct H9.
    - assert (imp_frame_z_rule (Seq_Stk i1 i2) fenv (minframe2 + frame - frame') (minframe2 + frame - frame' + frame'' - frame)).
      + econstructor.
        lia.
        eapply H10. lia.
        eapply timtowdi''. eapply H2. lia. lia. assert (minframe2 + frame - frame' + frame'' - frame = minframe2 + frame'' - frame') by lia. rewrite H22.
        assumption.
      + pose proof (H6 _ _ H22). rewrite H21. lia.
    - assert (imp_frame_z_rule (Seq_Stk i1 i2) fenv minframe1 (minframe1 + frame'' - frame)).
      + econstructor.
        assumption. eapply H20.
        pose proof (Z_le_gt_dec frame frame''). destruct H22.
        * lia.
        * pose proof (frame_cant_decrease_too_much _ _ _ _ H).
          assert (frame'' <= frame) by lia. specialize (H22 H23). clear H23.
          specialize (H22 _ _ H4).
          assert (minframe2 <= minframe1 + frame' - frame) by lia.
          pose proof (Z_le_gt_dec frame' frame''). destruct H24. lia. lia.
        * eassumption.
        * eapply timtowdi''. eapply H3. lia. lia.
      + invs H22. pose proof (H6 _ _ H22). lia.
  Qed.
  
  Lemma seq_zminframe_is_max :
    forall fenv i1 i2 frame frame' frame'',
      imp_frame_z_rule (Seq_Stk i1 i2) fenv frame frame'' ->
      imp_frame_z_rule i1 fenv frame frame' ->
      imp_frame_z_rule i2 fenv frame' frame'' ->
      forall minframe1 minframe2,
        (imp_frame_z_rule i1 fenv minframe1 (minframe1 + frame' - frame) /\
           forall f f',
             imp_frame_z_rule i1 fenv f f' -> minframe1 <= f) ->
        (imp_frame_z_rule i2 fenv minframe2 (minframe2 + frame'' - frame') /\
           forall f f',
             imp_frame_z_rule i2 fenv f f' -> minframe2 <= f) ->
        forall minframe,
          (imp_frame_z_rule (Seq_Stk i1 i2) fenv minframe (minframe + frame'' - frame) /\
             (forall f f' : Z,
                 imp_frame_z_rule (Seq_Stk i1 i2) fenv f f' -> minframe <= f)) ->
          minframe = Z.max minframe1 (minframe2 + frame - frame').
  Proof.
    intros. pose proof (Z_le_gt_dec frame frame'). destruct H5.
    - eapply seq_zminframe_leq_is_max; eassumption.
    - eapply seq_zminframe_gt_is_max; eassumption.
  Qed.

  Lemma imp_zframe_unfold_zero :
    forall i fenv frame f f' f'',
      imp_frame_z_rule
        i fenv
        (frame + f' - f)
        (frame + f'' - f) <->
      imp_frame_z_rule
        i fenv
        (frame + f' - f)
        (frame + f' - f + f'' - f').
  Proof.
    split; intros;
      assert (frame + f'' - f = frame + f' - f + f'' - f') by lia.
    - rewrite <- H0. assumption.
    - rewrite H0. assumption.
  Qed.

End Z_stk_frame.

