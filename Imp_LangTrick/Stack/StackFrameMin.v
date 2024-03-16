From Coq Require Import Arith Psatz Bool String List Nat Program.Equality ZArith.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
From Imp_LangTrick.Stack Require Import StackLanguage StackPure StackLangTheorems StackSemanticsMutInd StackFrame1 StackFrameMinHelpers.

Require Import Imp_LangTrick.LogicProp.LogicProp.

From Imp_LangTrick Require Import Stack.StackFrameZTheorems.

Local Definition P_min_frame (a: aexp_stack) (fenv: fun_env_stk) (frame: nat): Prop :=
  exists minframe,
    aexp_frame_rule a fenv minframe /\
      forall f,
        aexp_frame_rule a fenv f ->
        minframe <= f.
    
Local Definition P_frame_geq_preserved (a: aexp_stack) (fenv: fun_env_stk) (frame: nat): Prop :=
  forall stk1 stk2 n diff,
    aexp_stack_sem a fenv stk1 (stk2, n) ->
    frame + diff = Datatypes.length stk1 ->
    frame + diff = Datatypes.length stk2.

Local Definition P0_min_frame (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat): Prop :=
  exists minframe,
    args_frame_rule args fenv minframe /\
      forall f,
        args_frame_rule args fenv f ->
        minframe <= f.

Local Definition P0_frame_geq_preserved (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat): Prop :=
  forall stk1 stk2 vals diff,
    args_stack_sem args fenv stk1 (stk2, vals) ->
    frame + diff = Datatypes.length stk1 ->
    frame + diff = Datatypes.length stk2.

Local Definition P1_min_frame (b: bexp_stack) (fenv: fun_env_stk) (frame: nat) : Prop :=
  exists minframe,
    bexp_frame_rule b fenv minframe /\
      forall f,
        bexp_frame_rule b fenv f ->
        minframe <= f.

Local Definition P1_frame_geq_preserved (b: bexp_stack) (fenv: fun_env_stk) (frame: nat) : Prop :=
  forall stk1 stk2 v diff,
    bexp_stack_sem b fenv stk1 (stk2, v) ->
    frame + diff = Datatypes.length stk1 ->
    frame + diff = Datatypes.length stk2.

Local Definition P2_frame_geq_preserved (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat) : Prop :=
  forall stk1 stk2 diff,
    imp_stack_sem i fenv stk1 stk2 ->
    frame + diff = Datatypes.length stk1 ->
    frame' + diff =  Datatypes.length stk2.

Local Definition P2_min_frame (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat): Prop :=
  exists minframe,
    imp_frame_rule i fenv minframe ((minframe + frame') - frame) /\
      forall f f',
        imp_frame_rule i fenv f f' ->
        minframe <= f.


Lemma min_frame_seq (fenv : fun_env_stk)
      (frame : nat)
      (i1 i2 : imp_stack)
      (frame' frame'' : nat)
      (i : imp_frame_rule i1 fenv frame frame')
      (H : exists minframe : nat,
          imp_frame_rule i1 fenv minframe (minframe + frame' - frame) /\
            (forall f f' : nat, imp_frame_rule i1 fenv f f' -> minframe <= f))
      (i0 : imp_frame_rule i2 fenv frame' frame'')
      (H0 : exists minframe : nat,
          imp_frame_rule i2 fenv minframe (minframe + frame'' - frame') /\
            (forall f f' : nat, imp_frame_rule i2 fenv f f' -> minframe <= f)):
  exists minframe : nat,
    imp_frame_rule (Seq_Stk i1 i2) fenv minframe
                   (minframe + frame'' - frame) /\
      (forall f f' : nat,
          imp_frame_rule (Seq_Stk i1 i2) fenv f f' -> minframe <= f).
Proof.
  pose proof (imp_min_zframe).
  
  destruct H, H0. destruct H, H0.
  specialize (H1 _ _ _ _ (imp_nat_to_z_frame _ _ _ _ i)).
  destruct H1. destruct H1.
  pose proof (imp_min_zframe _ _ _ _ (imp_nat_to_z_frame _ _ _ _ i0)).
  destruct H5. destruct H5.
  pose proof (imp_min_zframe).
  specialize (H7 (Seq_Stk i1 i2) fenv (BinInt.Z.of_nat frame) (BinInt.Z.of_nat frame'')).
  assert (imp_frame_rule (Seq_Stk i1 i2) fenv frame frame'').
  econstructor.
  eassumption. assumption.
  eapply imp_nat_to_z_frame in H8. eapply H7 in H8. destruct H8.
  clear H7.
  destruct H8.  pose proof (imp_frame_z_rule_implies_nonneg_frame _ _ _ _ H7). destruct H9.
  pose proof (H7' := H7).
  eapply imp_z_to_nat_frame in H7. rewrite Znat.Z2Nat.inj_sub in H7.
  rewrite Znat.Z2Nat.inj_add in H7. rewrite Znat.Nat2Z.id in H7. rewrite Znat.Nat2Z.id in H7.
  2-4: lia.
  exists (BinInt.Z.to_nat x3).
  split.
  + assert (BinInt.Z.to_nat x3 + frame'' - frame = BinInt.Z.to_nat (BinInt.Z.sub (BinInt.Z.add x3 (BinInt.Z.of_nat frame''))
                                                                                 (BinInt.Z.of_nat frame))) by lia.
    rewrite H11.
    invs H7'.
    eapply imp_z_to_nat_frame.
    econstructor. assumption.
    eapply H15. assumption. assumption. assumption.
  + intros.
    eapply imp_nat_to_z_frame in H11. eapply H8 in H11. lia.
Qed.

       

Lemma min_frame :
  frame_rule_mut_ind_theorem P_min_frame P0_min_frame P1_min_frame P2_min_frame.
Proof.
  frame_rule_mutual_induction P P0 P1 P2 P_min_frame P0_min_frame P1_min_frame P2_min_frame; intros.
  - exists 0. split; intros.
    constructor. lia.
  - exists k. split; intros.
    constructor. auto. auto. invs H. auto.
  - destruct H. destruct H0. destruct H. destruct H0.
    exists (max x x0).
    split.
    + constructor. eapply aexp_frame_expansion. eapply H. lia.
      eapply aexp_frame_expansion. eapply H0. lia.
    + intros. invs H3. apply H1 in H6. apply H2 in H9. lia.
  - destruct H. destruct H0. destruct H. destruct H0.
    exists (max x x0).
    split.
    + constructor. eapply aexp_frame_expansion. eapply H. lia.
      eapply aexp_frame_expansion. eapply H0. lia.
    + intros. invs H3. apply H1 in H6. apply H2 in H9. lia.
  - destruct H1. destruct H0. destruct H. destruct H. destruct H0. destruct H1.
    exists x1. split.
    + eapply FrameApp with (func := func).
      assumption. assumption. assumption. assumption.
    + intros. eapply H2. invs H5. assumption.
  - exists 0. split.
    + constructor.
    + intros. lia.
  - destruct H. destruct H0. destruct H, H0.
    exists (max x x0).
    split.
    + constructor.
      * eapply aexp_frame_expansion.
        eassumption. lia.
      * eapply args_frame_expansion.
        eassumption.
        lia.
    + intros. invs H3. apply H1 in H6. apply H2 in H9. lia.
  - exists 0. split. constructor. lia.
  - exists 0. split. constructor. lia.
  - destruct H. destruct H. exists x. split.
    + constructor. assumption.
    + intros. invs H1. apply H0. assumption.
  - destruct H. destruct H0. destruct H, H0.
    exists (max x x0).
    split.
    + constructor; eapply bexp_frame_expansion; try eassumption; try lia.
    + intros. invs H3. apply H1 in H6. apply H2 in H9.
      lia.
  - destruct H. destruct H. destruct H0. destruct H0.
    exists (max x x0). split.
    + constructor; eapply bexp_frame_expansion; try eassumption; try lia.
    + intros. invs H3. apply H1 in H6. apply H2 in H9. lia.
  - destruct H, H0. destruct H, H0.
    exists (max x x0). split.
    + constructor; eapply aexp_frame_expansion; try eassumption; try lia.
    + intros. invs H3. apply H1 in H6. apply H2 in H9. lia.
  - destruct H, H0. destruct H, H0.
    exists (max x x0). split.
    + constructor; eapply aexp_frame_expansion; try eassumption; try lia.
    + intros. invs H3. apply H1 in H6. apply H2 in H9. lia.
  - exists 0. simpl. rewrite Nat.sub_diag. split. constructor.
    intros. lia.
  - destruct H. destruct H.
    exists (max k x).
    split.
    + rewrite Nat.add_sub. constructor.
      lia.
      enough (max k x = k \/ max k x = x).
      * destruct H1; lia.
      * pose proof (le_ge_dec k x). destruct H1; lia.
      * eapply aexp_frame_expansion. eapply H.
        lia.
    + intros. invs H1.
      eapply H0 in H9.
      lia.
  - exists 0. split.
    + simpl. rewrite Nat.add_comm, Nat.add_sub. constructor.
    + intros. lia.
  - exists 1. split; intros.
    + assert (1 + (frame - 1) - frame = 0) by lia.
      
      rewrite H. constructor. auto.
    + invs H. assumption.
  - eapply min_frame_seq; eassumption.
  
  - destruct H. destruct H0. destruct H1. exists (max (max x x0) x1).
    split; intros.
    + destruct H0, H1, H. econstructor.
      * eapply bexp_frame_expansion. eassumption. lia.
      * pose proof (le_ge_dec frame' frame). destruct H5.
        
        -- pose proof (frame_diff_cant_be_bigger_than_start).
           specialize (H5 _ _ _ _ i _ _ H0).
           destruct H5.
           ++ destruct H5. assert (frame' = frame) by lia.
              subst frame'.
              rewrite <- Nat.add_sub_assoc.
              rewrite Nat.sub_diag. rewrite <- (Nat.sub_diag x0).
              rewrite Nat.add_sub_assoc.
              rewrite Nat.add_sub in H0.
              eapply imp_frame_expansion.
              assumption. lia. auto. auto.
           ++ destruct H5. assert (x0 >= 1) by lia.
              assert (max (max x x0) x1 + frame' - frame = max (max x x0) x1 + (x0 + frame' - frame) - x0) by lia.
              rewrite H8. eapply imp_frame_expansion.
              assumption. lia.
        -- remember (x0 + frame' - frame) as x2.
           assert (frame' - frame = x2 - x0) by lia.
           rewrite <- Nat.add_sub_assoc.
           rewrite H5. rewrite Nat.add_sub_assoc.
           eapply imp_frame_expansion.
           assumption.
           lia. lia. assumption.
      * remember (x1 + frame' - frame) as x2.
        assert (frame' - frame = x2 - x1) by lia.
        pose proof (le_ge_dec frame' frame). destruct H6.
        -- pose proof (frame_diff_cant_be_bigger_than_start).
           specialize (H6 i2 _ _ _ i0 _ _ H1).
           destruct H6.
           ++ destruct H6. assert (frame' = frame) by lia.
              subst frame'. assert (x2 = x1) by lia.
              rewrite <- Nat.add_sub_assoc. rewrite Nat.sub_diag. rewrite <- (Nat.sub_diag x1). subst x2. rewrite Nat.add_sub in H1.
              rewrite Nat.add_sub_assoc. eapply imp_frame_expansion.
              assumption. lia. auto. auto.
           ++ destruct H6. assert (x1 >= 1) by lia.
              assert (max (max x x0) x1 + frame' - frame = max (max x x0) x1 + (x1 + frame' - frame) - x1) by lia.
              rewrite H9. eapply imp_frame_expansion.
              rewrite Heqx2 in H1.
              assumption. lia.
        -- rewrite <- Nat.add_sub_assoc.
           rewrite H5. rewrite Nat.add_sub_assoc.
           eapply imp_frame_expansion. assumption. lia. lia. assumption.
    + destruct H, H0, H1.
      invs H2. eapply H3 in H9. eapply H4 in H13. eapply H5 in H14. lia.
  - destruct H. destruct H0. rewrite Nat.add_sub in H0.
    destruct H0. exists (max x x0).
    split; intros.
    + rewrite Nat.add_sub. econstructor.
      * destruct H. eapply bexp_frame_expansion.
        eapply H. lia.
        
      * pose proof (imp_frame_expansion loop_body fenv).
        specialize (H2 x0 x0 H0 (max x x0)). rewrite Nat.add_sub in H2.
        apply H2. lia.
    + destruct H. invs H2. apply H3 in H6. apply H1 in H10. lia.
Qed.

Lemma aexp_min_frame :
  (forall (a : aexp_stack) (fenv : fun_env_stk) (frame : nat),
      aexp_frame_rule a fenv frame ->
      exists minframe : nat,
        aexp_frame_rule a fenv minframe /\
          (forall f : nat, aexp_frame_rule a fenv f -> minframe <= f)).
Proof.
  destruct min_frame. intuition.
Qed.

Lemma args_min_frame :
  (forall (args : list aexp_stack) (fenv : fun_env_stk) (frame : nat),
      args_frame_rule args fenv frame ->
      exists minframe : nat,
        args_frame_rule args fenv minframe /\
          (forall f : nat, args_frame_rule args fenv f -> minframe <= f)).
Proof.
  destruct min_frame. intuition.
Qed.

Lemma bexp_min_frame :
  (forall (b : bexp_stack) (fenv : fun_env_stk) (frame : nat),
      bexp_frame_rule b fenv frame ->
      exists minframe : nat,
        bexp_frame_rule b fenv minframe /\
          (forall f : nat, bexp_frame_rule b fenv f -> minframe <= f)).
Proof.
  destruct min_frame. intuition.
Qed.

Lemma imp_min_frame :
  (forall (i : imp_stack) (fenv : fun_env_stk) (frame frame' : nat),
      imp_frame_rule i fenv frame frame' ->
      exists minframe : nat,
        imp_frame_rule i fenv minframe (minframe + frame' - frame) /\
          (forall f f' : nat, imp_frame_rule i fenv f f' -> minframe <= f)).
Proof.
  destruct min_frame. intuition.
Qed.

Section min_frame_smaller_than_stack.
  Context (pminframe :=
             fun (P: nat -> Prop) (Q: nat -> Prop) =>
               exists minframe,
                 P minframe /\
                   (forall f,
                       Q f -> minframe <= f)).
  Let iminframe {i: imp_stack} {fenv: fun_env_stk} {frame frame': nat} (H: imp_frame_rule i fenv frame frame') : exists minframe, imp_frame_rule i fenv minframe (minframe + frame' - frame) /\ (forall f f': nat, imp_frame_rule i fenv f f' -> minframe <= f) :=
        imp_min_frame _ _ _ _ H.

  Let aexp_min a fenv fmin :=
        aexp_frame_rule a fenv fmin /\
          forall f,
            aexp_frame_rule a fenv f -> fmin <= f.
  Let bexp_min b fenv fmin :=
        bexp_frame_rule b fenv fmin /\
          forall f,
            bexp_frame_rule b fenv f -> fmin <= f.
  Let args_min args fenv fmin :=
        args_frame_rule args fenv fmin /\
          forall f,
            args_frame_rule args fenv f -> fmin <= f.
  Let imp_min i fenv frame frame' fmin :=
        imp_frame_rule i fenv fmin (fmin + frame' - frame) /\
          forall f f',
            imp_frame_rule i fenv f f' -> fmin <= f.

  Let P_smaller_than_min a fenv (frame: nat) :=
        forall fmin,
          aexp_min a fenv fmin ->
          (exists fake,
              aexp_frame_rule a fenv fake /\ fake < fmin) -> False.

  Let P0_smaller_than_min args fenv (frame: nat) :=
        forall fmin,
          args_min args fenv fmin ->
          (exists fake,
              args_frame_rule args fenv fake /\ fake < fmin) ->
          False.

  Let P1_smaller_than_min b fenv (frame: nat) :=
        forall fmin,
          bexp_min b fenv fmin ->
          (exists fake,
              bexp_frame_rule b fenv fake /\ fake < fmin) ->
          False.

  Let P2_smaller_than_min i fenv frame frame' :=
        forall fmin,
          imp_min i fenv frame frame' fmin ->
          (exists fake,
              imp_frame_rule i fenv fake (fake + frame' - frame) /\ fake < fmin) ->
          False.

  Lemma aexp_smaller_than_min_fake :
    forall a fenv frame,
      aexp_frame_rule a fenv frame ->
      P_smaller_than_min a fenv frame.
  Proof using P_smaller_than_min aexp_min.
    unfold P_smaller_than_min, aexp_min. intros.
    destruct H0. destruct H1. destruct H1. apply H2 in H1. lia.
  Qed.

  Lemma imp_smaller_than_min_fake :
    forall i fenv frame frame',
      imp_frame_rule i fenv frame frame' ->
      P2_smaller_than_min i fenv frame frame'.
  Proof using P2_smaller_than_min imp_min.
    unfold P_smaller_than_min, P0_smaller_than_min, P1_smaller_than_min, P2_smaller_than_min, aexp_min, bexp_min, imp_min, args_min; intros.
    destruct H0. destruct H1. destruct H1.
    apply H2 in H1. lia.
  Qed.

End min_frame_smaller_than_stack.

Lemma additive_identity :
  forall (n m: nat),
    n = m + n ->
    m = 0.
Proof.
  intros. lia.
Qed.

Lemma stack_mutated_at_index_preserved_by_sublist :
  forall (stk stk' other: stack) (k c: nat),
    1 <= k ->
    k <= Datatypes.length stk ->
    stack_mutated_at_index (stk' ++ other) k c (stk ++ other) ->
    stack_mutated_at_index stk' k c stk.
Proof.
  induction stk; intros.
  - simpl in H0. invs H0. lia.
  - simpl in H0.
    pose proof (MUT:= stack_mutated_at_index_preserves_length).
    specialize (MUT ((a :: stk) ++ other) (stk' ++ other) k c H1).
    rewrite app_length in MUT. rewrite app_length in MUT.
    apply Nat.add_cancel_r in MUT. simpl in MUT. destruct stk'; [ invs MUT | ].
    simpl in MUT.
    destruct k.
    + lia.
    + destruct k.
      * invs H1. econstructor.
        eapply app_inv_tail in H6. assumption.
        lia.
      * invs H1. simpl in H11. eapply IHstk in H11; [ | lia .. ].
        eapply stk_mut_rest; try lia.
        simpl. assumption.
Qed.

Lemma stack_mutated_at_index_preserved_by_superlist :
  forall (stk stk' other: stack) (k c: nat),
    stack_mutated_at_index stk' k c stk ->
    stack_mutated_at_index (stk' ++ other) k c (stk ++ other).
Proof.
  induction stk; intros.
  - invs H.
  - invs H.
    + simpl. constructor. reflexivity.
    + simpl. constructor.
      * assumption.
      * rewrite app_length. rewrite <- Nat.add_succ_l.
        lia.
      * repeat rewrite app_length. rewrite H4. reflexivity.
      * eapply IHstk. assumption.
      * reflexivity.
Qed.

Section IMP_STK_UNTOUCHED.
  Context (P_stk_untouched :=
             fun (i: imp_stack) (fenv: fun_env_stk) (stk stk': stack) =>
               forall (vals x stk1 stk2: stack) (frame frame': nat),
                 stk = vals ++ stk1 ->
                 stk' = x ++ stk1 ->
                 Datatypes.length x = frame' ->
                 imp_frame_rule i fenv frame frame' ->
                 Datatypes.length vals = frame ->
                 imp_stack_sem i fenv (vals ++ stk2 ++ stk1) (x ++ stk2 ++ stk1)).
  Context (P0_stk_untouched :=
             fun (a: aexp_stack) (fenv: fun_env_stk) (stk: stack)
               (stk'n: stack * nat) =>
               forall (stk': stack) (n: nat) (vals stk1 stk2: stack) (frame: nat),
                 stk = vals ++ stk1 ->
                 stk' = vals ++ stk1 ->
                 stk'n = (stk', n) ->
                 Datatypes.length vals = frame ->
                 aexp_frame_rule a fenv frame ->
                 aexp_stack_sem a fenv (vals ++ stk2 ++ stk1) (vals ++ stk2 ++ stk1, n)).
  Context (P1_stk_untouched :=
             fun (b: bexp_stack) (fenv: fun_env_stk) (stk: stack)
               (stk'v: stack * bool) =>
               forall (stk': stack) (v: bool) (vals stk1 stk2: stack) (frame: nat),
                 stk = vals ++ stk1 ->
                 stk' = vals ++ stk1 ->
                 stk'v = (stk', v) ->
                 Datatypes.length vals = frame ->
                 bexp_frame_rule b fenv frame ->
                 bexp_stack_sem b fenv (vals ++ stk2 ++ stk1) (vals ++ stk2 ++ stk1, v)).
  Context (P2_stk_untouched :=
             fun (args: list aexp_stack) (fenv: fun_env_stk) (stk: stack)
               (stk'vals: stack * (list nat)) =>
               forall (stk': stack) (vals: list nat) (x stk1 stk2: stack) (frame: nat),
                 stk = x ++ stk1 ->
                 stk' = x ++ stk1 ->
                 stk'vals = (stk', vals) ->
                 Datatypes.length x = frame ->
                 args_frame_rule args fenv frame ->
                 args_stack_sem args fenv (x ++ stk2 ++ stk1) (x ++ stk2 ++ stk1, vals)).

  Local Open Scope Z_scope.
  Local Open Scope nat_scope.



  Lemma nat_frame_stacks_zframes_same :
    forall (i3 : imp_stack) (fenv0 : fun_env_stk) (frame frame' : nat) (zframe zframe': Z) (stk stk': stack),
       imp_frame_rule i3 fenv0 frame frame' ->
       imp_stack_sem i3 fenv0 stk stk' ->
       zframe = Z.of_nat frame ->
       zframe' = Z.of_nat frame' ->
       (zframe' - zframe)%Z =
         ((Z.of_nat (Datatypes.length stk')) - (Z.of_nat (Datatypes.length stk)))%Z.
  Proof.
    intros. eapply stacks_zframes_same; eauto. 
    subst. apply imp_nat_to_z_frame. assumption.
  Qed.

  Lemma list_app_decomposition :
    forall (A: Type) (l: list A) (n1 n2: nat),
      Datatypes.length l = n1 + n2 ->
      Datatypes.length (firstn n1 l) = n1 /\ Datatypes.length (skipn n1 l) = n2.
  Proof.
    intros. rewrite skipn_length. rewrite firstn_length. split; lia.
  Qed.

  Lemma skipn_app_decomposition :
    forall (A: Type) (vals stk0 stk2: list A) (n m: nat),
      n = Datatypes.length vals ->
      skipn n (vals ++ stk0) = skipn m stk2 ->
      stk0 = skipn m stk2.
  Proof.
    intros. rewrite skipn_app in H0. rewrite H in H0.
    rewrite skipn_all in H0. simpl in H0.
    rewrite Nat.sub_diag in H0. assumption.
  Qed.

  Lemma skipn_app_decomposition' :
    forall (A: Type) (vals stk0 stk2: list A) (n m: nat),
      n = Datatypes.length vals ->
      skipn n (vals ++ stk0) = stk0.
  Proof.
    intros. rewrite skipn_app. rewrite H.
    rewrite skipn_all. simpl.
    rewrite Nat.sub_diag. auto.
  Qed.
  
  Lemma imp_stack_untouched_mut_ind :
    stack_sem_mut_ind_theorem P_stk_untouched P0_stk_untouched P1_stk_untouched P2_stk_untouched.
  Proof.
    stack_sem_mutual_induction P P0 P1 P2 P_stk_untouched P0_stk_untouched P1_stk_untouched P2_stk_untouched; intros.
    - invs H2. apply app_inv_tail in H0. rewrite H0. constructor.
    - invs H3.
      assert (vals ++ stk1 = stk') by (eapply aexp_frame_implies_pure; eassumption).
      symmetry in H0. subst stk'.
      pose proof (skip_n_of_mutated_stack k k c (vals ++ stk1)).
      specialize (H0 (x ++ stk1)).
      assert (k <= k) by auto.
      specialize (H0 H1 l l0 s).
      assert (k <= Datatypes.length vals) by (rewrite H11; assumption).
      symmetry in H11.
      eapply stack_mutated_at_index_preserved_by_sublist in s; [ | eassumption .. ].
    eapply stack_mutated_at_index_preserved_by_superlist with (other := stk2++ stk1) in s. econstructor.
      + assumption.
      + repeat rewrite app_length. rewrite Nat.add_assoc.
        lia.
      + eapply H. reflexivity. reflexivity. reflexivity. reflexivity.
        rewrite <- H11. assumption.
      + eassumption.
    - invs H2. rewrite app_comm_cons in H0. eapply app_inv_tail in H0. rewrite <- H0. simpl. constructor. reflexivity.
    - invs H2. rewrite app_comm_cons in H. eapply app_inv_tail in H. rewrite <- H. simpl. econstructor. reflexivity.
    - subst.
      invs H4.
      pose proof (imp_nat_to_z_frame).
      pose proof (H1 i1 _ _ _ H3).
      pose proof (stacks_zframes_same).
      cbn beta in H5.
      specialize (H5 _ _ _ _ i _ _ H2).
      rewrite app_length in H5.
      rewrite Nat2Z.inj_add in H5.
      rewrite Z.sub_add_distr in H5.
      remember (Z.of_nat (Datatypes.length vals)) as zvals.
      remember (Z.of_nat frame') as zframe.
      remember (Z.of_nat (Datatypes.length stk')) as zstk'.
      remember (Z.of_nat (Datatypes.length stk1)) as zstk1.
      pose proof (le_gt_dec (Datatypes.length vals) frame').
      assert (zstk' = zframe + zstk1)%Z as Hzstk' by lia.
      rewrite Heqzstk', Heqzframe, Heqzstk1 in Hzstk'.
      assert (Hstk' : Datatypes.length stk' = frame' + Datatypes.length stk1) by lia.
      eapply list_app_decomposition in Hstk'.
      destruct Hstk'.
      pose proof (Himp := imp_frame_implies_untouched_stack).
      specialize (Himp _ _ _ _ H3 _ _ i).
      eapply skipn_app_decomposition in Himp; eauto.
      pose proof (Happ := firstn_skipn frame' stk').
      symmetry in Happ. rewrite <- Himp in Happ.
      econstructor; eauto.
    - invs H4.
      assert (stk' = vals ++ stk1) by (symmetry; eapply bexp_frame_implies_pure; eassumption).
      subst stk'. econstructor; eauto.
    - invs H4. replace stk' with (vals ++ stk1) in * by (eapply bexp_frame_implies_pure; eassumption). 
      eapply Stack_if_false; eauto.
    - invs H3. econstructor.
      rewrite app_assoc.
      assert (vals ++ stk1 = x ++ stk1) by (eapply bexp_frame_implies_pure; eassumption).
      replace vals with x in *.
      rewrite <- app_assoc.
      eapply H; try eassumption; try reflexivity.
      eapply app_inv_tail in H0. symmetry. assumption.
    - inversion H5.
      replace stk with stk1 in * by (symmetry; eapply bexp_frame_implies_pure; eassumption).
      subst.
      symmetry in H12. rewrite H12 in *.
      pose proof (nat_frame_stacks_zframes_same).
      specialize (H2 _ _ _ _ _ _ _ _ H13 i0 eq_refl eq_refl).
      assert (Hlen : Datatypes.length stk2 = Datatypes.length (vals ++ stk0)) by lia.
      rewrite app_length in Hlen.
      pose proof (Hstk2 := list_app_decomposition).
      specialize (Hstk2 _ _ _ _ Hlen). destruct Hstk2 as [Hvals Hstk0].
      pose proof (Hstk2 := firstn_skipn (Datatypes.length vals) stk2).
      symmetry in Hstk2.
      pose proof (imp_frame_implies_untouched_stack).
      specialize (H3 _ _ _ _ H13 _ _ i0).
      eapply skipn_app_decomposition in H3; eauto. rewrite <- H3 in Hstk2.
      eapply Stack_while_step.
      + eapply H; auto.
      + eapply H0; try reflexivity.
        * eapply Hstk2.
        * rewrite Hvals. assumption.
      + rewrite Hstk2 in i1.
        eapply H1; try eauto.
    - invs H1. econstructor.
    - invs H1. econstructor.
      eassumption.
      rewrite app_length in l0. repeat rewrite app_length. rewrite Nat.add_assoc.
      lia.
      invs H3.
      erewrite nth_error_app1.
      erewrite nth_error_app1 in e. assumption. lia. lia.
    - invs H3. invc H5. clear H3.
      assert (stk1 = vals ++ stk0).
      symmetry; eapply aexp_frame_implies_pure.
      eapply H4. eassumption.
      subst stk1.
      econstructor; eauto.
    - invs H3. invs H5. clear H3.
      assert (stk1 = vals ++ stk0) by (symmetry; eapply aexp_frame_implies_pure; [ eapply H4 | eassumption ]).
      subst stk1.
      econstructor; eauto.
    - subst stk stk'. invc H4. invc H6.
      assert (stk1 = vals0 ++ stk0) by (symmetry; eapply args_frame_implies_pure; eassumption).
      subst stk1.
      assert (stk3 = stk2) by (symmetry; eapply aexp_frame_implies_pure; eassumption).
      subst stk3.
      pose proof (args_stack_sem_preserves_length).
      specialize (H2 _ _ _ _ _ a).
      pose proof (nat_frame_stacks_zframes_same).
      pose proof (Hiframe := H7).
      rewrite e3 in Hiframe.
      pose proof (same_after_popping_calculate_length).
      specialize (H3 _ _ _ _ _ _ _ _ H7 i eq_refl eq_refl).
      assert (Z.of_nat (Return_pop (fenv fname)) = Z.of_nat (Datatypes.length stk2) - Z.of_nat(Datatypes.length (vals ++ vals0 ++ stk0)))%Z by lia.
      assert (Datatypes.length stk2 = Return_pop (fenv fname) + Datatypes.length (vals ++ vals0 ++ stk0)) by lia.
      rewrite app_length in H8. rewrite Nat.add_assoc in H8. Set Printing All.
      replace (Nat.add (Return_pop (fenv fname)) (Datatypes.length vals)) with (Nat.add (Datatypes.length vals) (Return_pop (fenv fname))) in H8 by lia.
      Unset Printing All.
      apply list_app_decomposition in H8.
      pose proof (Hskipframe := imp_frame_implies_untouched_stack).
      pose proof (Hexp := imp_frame_expansion).
      specialize (Hexp _ _ _ _ H7 (Args (fenv fname) + Datatypes.length (vals0))).
      assert (Args (fenv fname) <= Args (fenv fname) + Datatypes.length vals0) by lia.
      specialize (Hexp H9). clear H9.
      repeat rewrite H2 in Hiframe.
      specialize (Hskipframe _ _ _ _ Hiframe _ _ i).
      eapply skipn_app_decomposition in Hskipframe; eauto.
      pose proof (Hstk2 := firstn_skipn (Datatypes.length vals + Return_pop (fenv fname)) stk2).
      rewrite <- Hskipframe in Hstk2.
      symmetry in Hstk2.
      rewrite app_assoc in Hstk2.
      econstructor.
      + reflexivity.
      + eassumption.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + eapply H; eauto.
      + rewrite app_assoc in i.
        rewrite app_assoc in H0.
        rewrite app_assoc.
        eapply H0.
        reflexivity.
        eassumption.
        reflexivity.
        destruct H8.
        rewrite e.
        rewrite app_length.
        rewrite e.
        replace (Args (fenv fname) + Datatypes.length vals0 + (Args (fenv fname) + Return_pop (fenv fname)) - Args (fenv fname)) with
          (Datatypes.length vals + Return_pop (fenv fname) + Datatypes.length vals0) in Hexp by lia.
        eassumption.
        rewrite app_length. f_equal.
        rewrite <- H2. symmetry. assumption.
      + eapply H1; eauto.
        eapply frame_expansion.
        eassumption. rewrite app_length. lia.
      + rewrite <- app_assoc.
        rewrite H2.
        destruct H8.
        eapply same_after_popping_length1.
        assumption. reflexivity.
    - invc H1. econstructor.
    - invc H1. econstructor.
    - invc H2. econstructor. eapply H. reflexivity. reflexivity. reflexivity. reflexivity.
      invs H4. assumption. reflexivity.
    - invc H3. invc H5.
      assert (stk' = vals ++ stk1) by (symmetry; eapply bexp_frame_implies_pure; [eapply H3 | eassumption ]).
      subst stk'.
      econstructor.
      + eapply H; eauto.
      + eapply H0; eauto.
      + reflexivity.
    - invc H3. invc H5.
      assert (stk' = vals ++ stk1) by (symmetry; eapply bexp_frame_implies_pure; [eapply H3 | eassumption ]).
      subst stk'.
      econstructor; eauto.
    - invc H3. invc H5. assert (stk' = vals ++ stk1) by (symmetry; eapply aexp_frame_implies_pure; [eapply H3 | eassumption ]).
      subst stk'.
      econstructor; eauto.
    - invc H3. invc H5. assert (stk' = vals ++ stk1) by (symmetry; eapply aexp_frame_implies_pure; [eapply H3 | eassumption ]).
      subst stk'.
      econstructor; eauto.
    - invc H1. econstructor.
    - invc H3. invc H5.
      assert (stk' = x ++ stk1) by (symmetry; eapply aexp_frame_implies_pure; eassumption).
      econstructor; eauto.
  Qed.

  Lemma imp_frame_stack_untouched :
     (forall (i : imp_stack) (fenv : fun_env_stk) (stk stk' : stack),
   imp_stack_sem i fenv stk stk' ->
   forall (vals x stk1 stk2 : stack) (frame frame' : nat),
   stk = vals ++ stk1 ->
   stk' = x ++ stk1 ->
   Datatypes.length x = frame' ->
   imp_frame_rule i fenv frame frame' ->
   Datatypes.length vals = frame -> imp_stack_sem i fenv (vals ++ stk2 ++ stk1) (x ++ stk2 ++ stk1)).
  Proof.
    eapply imp_stack_untouched_mut_ind.
  Qed.

End IMP_STK_UNTOUCHED.

Lemma frame_implies_intervening_stk_okay :
  forall i frame frame' fenv stk1 stk1' stk2 stk3,
    imp_frame_rule i fenv frame (frame + frame') ->
    frame = Datatypes.length stk1 ->
    (frame + frame') = Datatypes.length stk1' ->
    imp_stack_sem i fenv (stk1 ++ stk3) (stk1' ++ stk3) ->
    imp_stack_sem i fenv (stk1 ++ stk2 ++ stk3) (stk1' ++ stk2 ++ stk3).
Proof.
  intros.
  eapply imp_frame_stack_untouched.
  + eassumption.
  + reflexivity.
  + reflexivity.
  + symmetry. eassumption.
  + eassumption.
  + symmetry. eassumption.
Qed.

Ltac simplify_stacks :=
  match goal with
  | [ H: aexp_frame_rule ?a ?fenv _,
        H': aexp_stack_sem ?a ?fenv ?stk (?stk', _) |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk = stk') by (eapply aexp_frame_implies_pure; eassumption);
      rewrite <- same in *; clear same
  | [ H: bexp_frame_rule ?b ?fenv _,
        H': bexp_stack_sem ?b ?fenv ?stk (?stk', _) |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk = stk') by (eapply bexp_frame_implies_pure; eassumption);
      rewrite <- same in *; clear same
  | [ H: args_frame_rule ?args ?fenv _,
        H' : args_stack_sem ?args ?fenv ?stk (?stk', _) |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk = stk') by (eapply args_frame_implies_pure; eassumption);
      rewrite <- same in *; clear same
  end.

Ltac simplify_stacks' :=
  match goal with
  | [ H: aexp_frame_rule ?a ?fenv _,
        H': aexp_stack_sem ?a ?fenv ?stk (?stk', _) |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk = stk') by (eapply aexp_frame_implies_pure; eassumption);
      rewrite same in *; clear same
  | [ H: bexp_frame_rule ?b ?fenv _,
        H': bexp_stack_sem ?b ?fenv ?stk (?stk', _) |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk = stk') by (eapply bexp_frame_implies_pure; eassumption);
      rewrite same in *; clear same
  | [ H: args_frame_rule ?args ?fenv _,
        H' : args_stack_sem ?args ?fenv ?stk (?stk', _) |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk = stk') by (eapply args_frame_implies_pure; eassumption);
      rewrite same in *; clear same
  end.

Lemma list_app_same_implies_other_same_sym :
  forall (A: Type) (l1 l2 l3: list A),
    l2 ++ l1 = l2 ++ l3 ->
    l1 = l3.
Proof.
  intros A l1 l2. revert l1. induction l2; intros; auto.
  simpl in H. inversion H. eapply IHl2; eauto. 
Qed.

Lemma rev_inj :
  forall (A : Type) (l1 l2 : list A),
    rev l1 = rev l2 ->
    l1 = l2.
Proof.
  intros. 
  replace l1 with (rev (rev l1)) by apply rev_involutive.
  replace l2 with (rev (rev l2)) by apply rev_involutive.
  f_equal. auto.
Qed.

Ltac replace_lists l1 l2 H :=
  replace (l1 ++ l2) with (rev (rev (l1 ++ l2))) in H by apply rev_involutive;
  replace (rev (l1 ++ l2)) with (rev l2 ++ rev l1) in H by (symmetry; apply rev_app_distr).

Lemma list_app_same_implies_other_same :
  forall (A: Type) (l1 l2 l3: list A),
    l1 ++ l2 = l3 ++ l2 ->
    l1 = l3.
Proof.
  intros. replace_lists l1 l2 H. replace_lists l3 l2 H.
  apply rev_inj.
  eapply list_app_same_implies_other_same_sym.
  eapply rev_inj.
  eauto. 
Qed.


Lemma neq_successor:
  forall (n: nat),
    n = S n ->
    False.
Proof.
  induction n; intros.
  - invs H.
  - invs H. eapply IHn in H1. invs H1.
Qed.

Lemma successor_not_leq :
  forall (n: nat),
    S n <= n ->
    False.
Proof.
  induction n; intros.
  - invs H.
  - assert (S n <= n) by lia.
    apply IHn in H0. assumption.
Qed.

Lemma n_eq_m_plus_n_implies_m_zero :
  forall (n m: nat),
    n = m + n ->
    m = 0.
Proof.
  induction n; intros.
  - rewrite Nat.add_0_r in H.
    symmetry in H. assumption.
  - apply IHn.
    rewrite Nat.add_succ_r in H.
    invs H. rewrite <- H1. assumption.
Qed.

Lemma list_length_zero_implies_nil_list :
  forall A (l: list A),
    Datatypes.length l = 0 ->
    l = nil.
Proof.
  destruct l; intros.
  - reflexivity.
  - inversion H.
Qed.

Lemma addition_elimination :
  forall (n1 n2 n3: nat),
    n1 + n3 = n2 + n3 ->
    n1 = n2.
Proof.
  induction n1; intros.
  - simpl in H. apply n_eq_m_plus_n_implies_m_zero in H. symmetry in H. assumption.
  - destruct n2.
    + rewrite Nat.add_0_l in H. symmetry in H.
      apply n_eq_m_plus_n_implies_m_zero in H. assumption.
    + f_equal.
      apply IHn1 with (n3 := S n3).
      repeat rewrite Nat.add_succ_r.
      lia.
Qed.

  
Lemma stack_mutated_prefix_OK:
  forall x' x stk k c,
    k <= Datatypes.length x ->
    stack_mutated_at_index (x' ++ stk) k c (x ++ stk) <->
    stack_mutated_at_index x' k c x.
Proof.
  induction x'; intros; split; intros.
  - invs H0.
    + simpl in H2.
      rewrite <- H2 in H1.
      assert (Datatypes.length (n0 :: stk') = Datatypes.length (x ++ (c :: stk'))).
      {
        f_equal. 
        assumption.
      }
      destruct x; [ | simpl in H3; invs H3 ].
      invs H.
      rewrite app_length in H5.
      simpl in H5. destruct (Datatypes.length x).
      * simpl in H5. apply neq_successor in H5. invs H5.
      * assert (S (Datatypes.length  stk') <= S n1 + S (Datatypes.length stk')) by lia.
        rewrite <- H5 in H2.
        apply successor_not_leq in H2.
        inversion H2.
    + simpl in H6. rewrite <- H6 in H1.
      assert (Datatypes.length (n' :: stk') = Datatypes.length (x ++ n' :: stk0)) by (f_equal; assumption).
      rewrite app_length in H7. simpl in H7.
      rewrite H4 in H7.
      apply n_eq_m_plus_n_implies_m_zero in H7.
      apply list_length_zero_implies_nil_list in H7. subst.
      simpl in H1. simpl in *.
      invs H0. invs H2. invs H7.
      invs H. invs H2.
  - invs H0.
  - destruct x. simpl in H.  invs H. invs H0.  invs H3.
    revert H. revert H0. induction k; intros.
    + invs H0. invs H5.
    + pose proof (Nat.eq_decidable a n).
      unfold Decidable.decidable in H1. destruct H1.
      * subst. invs H0.
        -- apply list_app_same_implies_other_same in H5. subst.
           constructor. reflexivity.
        -- repeat rewrite app_length in H9.
           apply addition_elimination in H9.
           eapply IHx' in H10.
           constructor. assumption.
           simpl in H.
           
           rewrite H9. simpl in H.
           assumption.
           assumption.
           assumption.
           assumption.
           simpl in H. lia.
      * invs H0.
        apply list_app_same_implies_other_same in H6. subst. constructor.
        reflexivity.
        unfold not in H1.
        assert (n = n) by reflexivity.
        apply H1 in H2. inversion H2.
  - invs H0.
    + constructor. reflexivity.
    + eapply IHx' with (stk := stk) in H6; [ | simpl in H; lia ].
      repeat rewrite <- app_comm_cons.
      constructor.
      * assumption.
      * rewrite app_length. lia.
      * repeat rewrite app_length. rewrite H5. reflexivity.
      * assumption.
      * reflexivity.
Qed.

Lemma app_decomposition :
  forall A (x y a b : list A),
    x ++ y = a ++ b ->
    Datatypes.length x = Datatypes.length a ->
    x = a /\ y = b.
Proof.
  induction x; intros.
  -  simpl in H0. symmetry in H0. apply list_length_zero_implies_nil_list in H0. subst. simpl in H. split; [ reflexivity | assumption ].
  - destruct a0; [ invs H0 | ].
    simpl in H0. invs H0.
    simpl in H.
    invs H.
    apply IHx in H4; [ | assumption ].
    destruct H4 as (H3 & H4).
    split.
    + f_equal. assumption.
    + assumption.
Qed.

Lemma add_has_unique_identity :
  forall (m n: nat),
    n + m = m ->
    n = 0.
Proof.
  induction m; intros.
  - rewrite Nat.add_0_r in H. assumption.
  - rewrite Nat.add_succ_r in H. invs H. apply IHm in H1. assumption.
Qed.

Lemma app_cons_help :
  forall A (l1 l2: list A) (x: A),
    l1 ++ (x :: l2) = (l1 ++ (x :: nil)) ++ l2.
Proof.
  induction l1; intros.
  - simpl. reflexivity.
  - simpl.
    f_equal. apply IHl1.
Qed.

    
Lemma app_decomposition' :
  forall A (y x a b : list A),
    x ++ y = a ++ b ->
    Datatypes.length y = Datatypes.length b ->
    x = a /\ y = b.
Proof.
  induction y; intros.
  - rewrite app_nil_r in H. simpl in H0. destruct b; [ | invs H0 ]. rewrite app_nil_r in H.
    split; auto.
  - simpl in H0. destruct b; [ invs H0 | ].
    
    destruct a0.
    + simpl in H. rewrite <- app_nil_l in H. simpl in H0. invs H0.
      rewrite app_cons_help in H. rewrite (app_cons_help A nil b a1) in H.
      apply IHy in H; [ | assumption ].
      destruct H.
      simpl in H. rewrite <- app_nil_l in H. destruct x; [ | invs H]. simpl in H. invs H. split; reflexivity.
      assert (Datatypes.length (A := A) (x ++ (a :: nil)) = Datatypes.length (A := A) nil).
      f_equal. assumption.
      simpl in H1. destruct x; [ | invs H1 ].
      simpl in H5. invs H5.
    + rewrite app_cons_help in H. rewrite (app_cons_help A (a0 :: a2) b a1) in H.
      apply IHy in H.
      destruct H.
      assert (Datatypes.length (A := A) (x ++ a :: nil) = Datatypes.length (A := A) ((a0 :: a2) ++ (a1 :: nil))).
      f_equal. assumption.
      destruct x.
      * simpl in H2. rewrite app_length in H2. simpl in H2. rewrite Nat.add_1_r in H2. invs H2.
      * rewrite app_length in H2. rewrite app_length in H2. simpl in H2.
        invs H2. repeat rewrite Nat.add_1_r in H4. invs H4.
        apply app_decomposition in H; [ | simpl; f_equal; assumption ].
        destruct H. invs H1. split.
        assumption. reflexivity.
      * simpl in H0. invs H0. reflexivity.
Qed.
    

Lemma same_after_popping_decomposition :
  forall stk stk' n,
    same_after_popping stk' stk n ->
    stk = (firstn n stk) ++ stk'.
Proof.
  induction stk; intros.
  - invs H. simpl. reflexivity.
  - invs H.
    + reflexivity.
    + simpl. f_equal. eapply IHstk. assumption.
Qed.

Definition frame_rule_length_P (i: imp_stack) (fenv: fun_env_stk) (stk stk': stack): Prop :=
  forall frame frame',
    imp_frame_rule i fenv frame frame' ->
    Datatypes.length stk >= frame ->
    exists x x' y,
      Datatypes.length x = frame /\
        Datatypes.length x' = frame' /\
        x ++ y = stk /\
        x' ++ y = stk'.

Definition frame_rule_length_P0 (a: aexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'v: stack * nat): Prop :=
  forall frame stk' v,
    stk'v = (stk', v) ->
    aexp_frame_rule a fenv frame ->
    Datatypes.length stk >= frame ->
    exists x y,
      Datatypes.length x = frame /\
        x ++ y = stk /\
        x ++ y = stk'.

Definition frame_rule_length_P1 (b: bexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'v: stack * bool): Prop :=
  forall frame stk' v,
    stk'v = (stk', v) ->
    bexp_frame_rule b fenv frame ->
    Datatypes.length stk >= frame ->
    exists x y,
      Datatypes.length x = frame /\
        x ++ y = stk /\
        x ++ y = stk'.

Definition frame_rule_length_P2 (args: list aexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'vals: stack * (list nat)): Prop :=
  forall frame stk' vals,
    stk'vals = (stk', vals) ->
    args_frame_rule args fenv frame ->
    Datatypes.length stk >= frame ->
    exists x y,
      Datatypes.length x = frame /\
        x ++ y = stk /\
        x ++ y = stk'.

Ltac split_helper :=
  match goal with
  | [ |- _ /\ _ ] =>
      split; [ | split_helper ]
  | _ =>
      idtac
  end.

Ltac destruct_exists_helper H :=
  let typeH := type of H in
  match typeH with
  | exists x, _ =>
      let newX := fresh x in
      destruct H as (newX & H);
      destruct_exists_helper H
  | _ /\ _ =>
      let newA := fresh "A" in
      destruct H as (newA & H);
      destruct_exists_helper H
  | _ =>
      idtac
  end.

Ltac destruct_exists :=
  match goal with
  | [ H: exists x, _ |- _ ] =>
      destruct_exists_helper H
  end.

Ltac f_equal_bck myfun H :=
  match goal with
  | [ H' : ?x = ?y |- _ ] =>
      match H' with
      | H =>
          assert (myfun x = myfun y) by (f_equal; assumption)
      end
  end.

Lemma skipn_app :
  forall A (x y: list A) (n: nat),
    Datatypes.length x = n ->
    skipn n (x ++ y) = y.
Proof.
  induction x; intros.
  - simpl. simpl in H. rewrite <- H. simpl. reflexivity.
  - simpl. destruct n. invs H.
    simpl. apply IHx. simpl in H. lia.
Qed.

Lemma frame_rule_length :
  stack_sem_mut_ind_theorem frame_rule_length_P frame_rule_length_P0 frame_rule_length_P1 frame_rule_length_P2.
Proof.
  stack_sem_mutual_induction P P0 P1 P2 frame_rule_length_P frame_rule_length_P0 frame_rule_length_P1 frame_rule_length_P2; intros.
  - invs H. exists (firstn frame' stk).
    exists (firstn frame' stk).
    exists (skipn frame' stk).
    split; [ | split; [ | split ]].
    + apply firstn_length_le. lia.
    + apply firstn_length_le. lia.
    + apply firstn_skipn.
    + apply firstn_skipn.
  - invs H0.
    pose proof (STACK := s).
    eapply stack_mutated_at_index_preserves_length in s.
    simplify_stacks.
    eapply H in H9; [ | eapply eq_refl | assumption ].
    destruct H9. destruct H2.
    rewrite <- (firstn_skipn frame' stk) in STACK.
    apply stack_mutation_app in STACK.
    destruct_exists.
    destruct_exists_helper H2.
    rewrite <- A0 in STACK.
    rewrite <- H2 in H1.
    rewrite <- H2.
    exists x.
    exists (stk0' ++ (c :: stk0'')).
    exists x0.
    split_helper.
    + assumption.
    + assert (Datatypes.length stk'' = Datatypes.length (stk0' ++ (c :: stk0'') ++ skipn frame' (x ++ x0))).
      f_equal. assumption.
      rewrite s in H3. rewrite app_length in H3. rewrite app_length in H3.
      rewrite app_length.
      rewrite <- A0 in H3. rewrite app_length in H3. rewrite Nat.add_assoc in H3.
      rewrite skipn_app in H3.
      apply addition_elimination in H3. rewrite <- H3. assumption. assumption.
    + reflexivity.
    + rewrite STACK. rewrite app_assoc. f_equal.
      rewrite skipn_app. reflexivity. assumption.
    + rewrite firstn_length_le. assumption.
      assumption.
  - subst.
    invs H.
    exists (firstn frame stk).
    exists (firstn (frame + 1) (0 :: stk)).
    exists (skipn frame stk).
    split; [ | split; [ | split ]].
    + apply firstn_length_le. assumption.
    + apply firstn_length_le. simpl. rewrite Nat.add_1_r. eapply le_n_S.
      assumption.
    + apply firstn_skipn.
    + assert (skipn (frame + 1) (0 :: stk) = skipn frame stk).
      rewrite Nat.add_1_r. simpl. reflexivity.
      rewrite <- H1. apply firstn_skipn.
  - subst. invs H.
    exists (firstn frame (v :: stk')).
    exists (firstn (frame - 1) stk').
    exists (skipn frame (v :: stk')).
    assert (exists x, frame = S x) by (apply geq_one_implies_successor; assumption).
    destruct H2.
    subst.
    rewrite <- Nat.add_1_r. rewrite Nat.add_sub.
    split; [ | split; [ | split ]].
    + rewrite Nat.add_1_r.
      simpl. f_equal.
      apply firstn_length_le.
      simpl in H0. lia.
    + simpl in H0. apply firstn_length_le. lia.
    + apply firstn_skipn.
    + rewrite Nat.add_1_r. simpl. apply firstn_skipn.
  - invs H1. eapply H in H5; [ | assumption ].
    eapply H0 in H9.
    destruct H5 as (x1 & x1' & y1 & A1 & B1 & C1 & D1).
    destruct H9 as (x2 & x2' & y2 & A2 & B2 & C2 & D2).
    rewrite <- C2 in D1.
    apply app_decomposition in D1; [ | rewrite A2; assumption ].
    destruct D1. subst.
    
    exists x1. exists x2'. exists y2.
    split; [ | split; [ | split ]]; reflexivity.
    destruct H5 as (x1 & x1' & y1 & A1 & B1 & C1 & D1).
    rewrite <- D1.
    rewrite app_length.
    rewrite B1.
    lia.
  - invs H1.
    eapply H in H6; [ | eapply eq_refl | eassumption ].
    destruct H6 as (x & y & A & B & C).
    eapply H0 in H10; [ | rewrite <- C; rewrite app_length; lia ].
    destruct H10 as (x1 & x1' & y1 & D & E & F & G).
    rewrite <- C in F.
    apply app_decomposition in F; [ | rewrite A ; rewrite D; reflexivity ].
    destruct F as (F1 & F2).
    subst.
    exists x. exists x1'. exists y.
    split; [ | split; [ | split]]; reflexivity.
  - invs H1.
    invs H1.
    eapply H in H6; [ | eapply eq_refl | eassumption ].
    destruct H6 as (x & y & A & B & C).
    eapply H0 in H11; [ | rewrite <- C; rewrite app_length; lia ].
    destruct H11 as (x1 & x1' & y1 & D & E & F & G).
    rewrite <- C in F.
    apply app_decomposition in F; [ | rewrite A ; rewrite D; reflexivity ].
    destruct F as (F1 & F2).
    subst.
    exists x. exists x1'. exists y.
    split; [ | split; [ | split]]; reflexivity.
  - invs H0.
    eapply H in H4; [ | eapply eq_refl | eassumption ].
    destruct H4 as (x & y & A & B & C).
    exists x. exists x. exists y.
    split; [ | split; [ | split ]]; assumption.
  - invs H2.
    eapply H in H6; [ | eapply eq_refl | eassumption ].
    eapply H0 in H10; destruct H6 as (x & y & A & B & C).
    destruct H10 as (x1 & x1' & y1 & D & E & F & G).
    rewrite <- C in F.
    eapply app_decomposition in F.
    destruct F.
    subst.
    eapply H1 in H2.
    destruct H2 as (x2 & x2' & y2 & F & G & I & J).
    rewrite <- J.
    rewrite <- E in F.
    apply app_decomposition in I; [ | assumption ].
    destruct I.
    subst.
    exists x. exists x2'. exists y.
    split; [ | split; [ | split ]]; [ | assumption | .. ]; reflexivity.
    rewrite app_length. rewrite E. lia.
    rewrite D. rewrite A. reflexivity.
    rewrite <- C. rewrite app_length. lia.
  - invs H.
    remember (skipn frame stk') as y.
    remember (firstn frame stk') as x.
    exists x. exists y.
    split_helper; subst.
    apply firstn_length_le.
    assumption.
    apply firstn_skipn.
    apply firstn_skipn.
  - invs H. remember (skipn frame stk') as y.
    remember (firstn frame stk') as x.
    exists x. exists y.
    split_helper; subst.
    apply firstn_length_le.
    assumption.
    apply firstn_skipn.
    apply firstn_skipn.
  - invs H1.
    invs H2.
    simplify_stacks.
    apply H with (stk' := stk1) (v := n1) in H6.
    assumption. reflexivity.
    assumption.
  - invs H1. invs H2.
    simplify_stacks.
    apply H with (stk' := stk1) (v:= n1) in H6.
    assumption.
    reflexivity.
    assumption.
  - invs H2.
    invs H3.
    apply H with (stk' := stk1) (vals := vals) in H7; auto.
    destruct_exists.
    apply H0 with (frame := (Args (fenv fname))) (frame' := (Args (fenv fname) + Return_pop (fenv fname))) in H9.
    destruct_exists.
    apply H1 with (stk' := stk3) (v := v) in H12.
    apply args_stack_sem_preserves_length in a.
    rewrite e3 in *. rewrite a in *.
    apply app_decomposition in A3; [ | assumption ].
    destruct A3.
    subst.
    destruct_exists.
    rewrite <- A2 in A.
    apply app_decomposition in A0; [ | assumption ].
    destruct A0. subst.
    apply same_after_popping_length in s.
    subst.
    exists x. exists y.
    split_helper; reflexivity.
    assumption.
    reflexivity.
    rewrite <- A2.
    rewrite <- H9.
    rewrite app_length.
    lia.
    rewrite e3. apply args_stack_sem_preserves_length in a.
    rewrite app_length. rewrite a. lia.
  - invs H.
    exists (firstn frame stk'). exists (skipn frame stk').
    split_helper.
    + apply firstn_length_le. assumption.
    + apply firstn_skipn.
    + apply firstn_skipn.
  - invs H. exists (firstn frame stk'). exists (skipn frame stk').
    split_helper; [ | apply firstn_skipn .. ].
    apply firstn_length_le. assumption.
  - invs H1. eapply H. invs H0.
    eapply eq_refl.
    eassumption.
    assumption.
  - invs H2. invs H1.
    eapply H0 with (stk' := stk'0) in H9.
    eapply H with (stk' := stk') in H6.
    destruct_exists.
    destruct_exists.
    rewrite <- A0 in H6.
    apply app_decomposition in H6.
    destruct H6.
    subst. exists x. exists y.
    split_helper; reflexivity.
    rewrite A. rewrite A1. reflexivity.
    eapply eq_refl.
    assumption.
    eauto.
    apply H with (stk' := stk') (v := b1) in H6.
    destruct_exists.
    rewrite <- H6. rewrite app_length.
    rewrite A. lia.
    reflexivity.
    assumption.
  - invs H2. invs H1.
    eapply H0 with (stk' := stk'0) in H9.
    eapply H with (stk' := stk') in H6.
    destruct_exists.
    destruct_exists.
    rewrite <- A0 in H6.
    apply app_decomposition in H6.
    destruct H6.
    subst. exists x. exists y.
    split_helper; reflexivity.
    rewrite A. rewrite A1. reflexivity.
    eapply eq_refl.
    assumption.
    eauto.
    apply H with (stk' := stk') (v := b1) in H6.
    destruct_exists.
    rewrite <- H6. rewrite app_length.
    rewrite A. lia.
    reflexivity.
    assumption.
  - invs H1.  invs H2.
    eapply H0 with (stk' := stk'0) in H9.
    eapply H with (stk' := stk') in H6.
    destruct_exists.
    destruct_exists.
    rewrite <- A0 in H6.
    apply app_decomposition in H6.
    destruct H6.
    subst. exists x. exists y.
    split_helper; reflexivity.
    rewrite A. rewrite A1. reflexivity.
    eapply eq_refl.
    assumption.
    eauto.
    apply H with (stk' := stk') (v := n1) in H6.
    destruct_exists.
    rewrite <- H6. rewrite app_length.
    rewrite A. lia.
    reflexivity.
    assumption.
  - invs H1.  invs H2.
    eapply H0 with (stk' := stk'0) in H9.
    eapply H with (stk' := stk') in H6.
    destruct_exists.
    destruct_exists.
    rewrite <- A0 in H6.
    apply app_decomposition in H6.
    destruct H6.
    subst. exists x. exists y.
    split_helper; reflexivity.
    rewrite A. rewrite A1. reflexivity.
    eapply eq_refl.
    assumption.
    eauto.
    apply H with (stk' := stk') (v := n1) in H6.
    destruct_exists.
    rewrite <- H6. rewrite app_length.
    rewrite A. lia.
    reflexivity.
    assumption.
  - invs H.
    exists (firstn frame stk'). exists (skipn frame stk').
    split_helper; [ | apply firstn_skipn .. ].
    apply firstn_length_le. assumption.
  - invs H1. invs H2.
    apply H with (stk' := stk') (v := val) in H6; apply H0 with (stk' := stk'0) (vals := vals) in H9.
    destruct_exists. destruct_exists.
    rewrite <- A0 in H6.
    apply app_decomposition in H6. destruct H6. subst.
    exists x. exists y.
    split_helper; reflexivity.
    rewrite A1. rewrite A. reflexivity.
    reflexivity.
    destruct_exists.
    rewrite <- H6. rewrite A0. assumption.
    reflexivity.
    reflexivity.
    apply H with (stk' := stk') (v := val) in H6. destruct_exists.
    rewrite <- H6. rewrite A0. assumption.
    reflexivity.
    assumption.
    assumption.
    reflexivity.
    eapply H with (stk' := stk') in H6.
    destruct_exists. rewrite <- H6. rewrite A0. assumption.
    eauto.
    assumption.
Qed.

Lemma imp_frame_rule_length :
  forall (i : imp_stack) (fenv : fun_env_stk) (stk stk' : stack),
   imp_stack_sem i fenv stk stk' ->
   forall frame frame' : nat,
   imp_frame_rule i fenv frame frame' ->
   Datatypes.length stk >= frame ->
   exists x x' y : list nat, Datatypes.length x = frame /\ Datatypes.length x' = frame' /\ x ++ y = stk /\ x' ++ y = stk'.
Proof.
  pose proof (frame_rule_length) as P.
  unfold stack_sem_mut_ind_theorem in P. destruct P as (IMP & _).
  eapply IMP.
Qed.

Lemma aexp_frame_rule_length :
  forall (a : aexp_stack) (fenv : fun_env_stk) (stk : stack) (stk' : stack) (n : nat),
    aexp_stack_sem a fenv stk (stk', n) ->
    forall (frame : nat),
      aexp_frame_rule a fenv frame ->
      Datatypes.length stk >= frame -> exists x y : list nat, Datatypes.length x = frame /\ x ++ y = stk /\ x ++ y = stk'.
Proof.
  pose proof (frame_rule_length) as P.
  unfold stack_sem_mut_ind_theorem in P. destruct P as (_ & AEXP & _).
  intros. eapply AEXP; eauto.
Qed.

Lemma bexp_frame_rule_length:
  forall (b : bexp_stack) (fenv : fun_env_stk) (stk : stack) (stk' : stack) (v: bool),
    bexp_stack_sem b fenv stk (stk', v) ->
    forall (frame : nat),
      bexp_frame_rule b fenv frame ->
      Datatypes.length stk >= frame -> exists x y : list nat, Datatypes.length x = frame /\ x ++ y = stk /\ x ++ y = stk'.
Proof.
  pose proof (frame_rule_length) as P.
  unfold stack_sem_mut_ind_theorem in P. destruct P as (_ & _ & BEXP & _).
  intros. eapply BEXP; eauto.
Qed.

Lemma args_frame_rule_length :
  forall (args : list aexp_stack) (fenv : fun_env_stk) (stk : stack) (stk': stack) (vals : list nat),
    args_stack_sem args fenv stk (stk', vals) ->
    forall (frame : nat),
      args_frame_rule args fenv frame ->
      Datatypes.length stk >= frame -> exists x y : list nat, Datatypes.length x = frame /\ x ++ y = stk /\ x ++ y = stk'.
Proof.
  pose proof (frame_rule_length) as P.
  unfold stack_sem_mut_ind_theorem in P. destruct P as (_ & _ & _ & ARGS).
  intros. eapply ARGS; eauto.
Qed.

Definition P_aexp_frame_pure_mut (i: imp_stack) (fenv: fun_env_stk) (stk stk': stack): Prop :=
  forall frame frame' x stk1 stk2,
    imp_frame_rule i fenv frame frame' ->
    stk = stk1 ++ x ->
    stk' = stk2 ++ x ->
    Datatypes.length stk1 = frame ->
    Datatypes.length stk2 = frame' ->
    forall x',
      imp_stack_sem i fenv (stk1 ++ x') (stk2 ++ x').

Definition P0_aexp_frame_pure_mut (a: aexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'v: stack * nat): Prop :=
  forall frame x stk' v stk1,
    aexp_frame_rule a fenv frame ->
    stk'v = (stk', v) ->
    stk = stk1 ++ x ->
    stk' = stk1 ++ x ->
    Datatypes.length stk1 = frame ->
    forall x',
      aexp_stack_sem a fenv (stk1 ++ x') (stk1 ++ x', v).

Definition P1_aexp_frame_pure_mut (b: bexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'v: stack * bool): Prop :=
  forall frame x stk' v stk1,
    bexp_frame_rule b fenv frame ->
    stk'v = (stk', v) ->
    stk = stk1 ++ x ->
    stk' = stk1 ++ x ->
    Datatypes.length stk1 = frame ->
    forall x',
      bexp_stack_sem b fenv (stk1 ++ x') (stk1 ++ x', v).

Definition P2_aexp_frame_pure_mut (args: list aexp_stack) (fenv: fun_env_stk) (stk: stack) (stk'vals: stack * (list nat)): Prop :=
  forall frame x stk' vals stk1,
    args_frame_rule args fenv frame ->
    stk'vals = (stk', vals) ->
    stk = stk1 ++ x ->
    stk' = stk1 ++ x ->
    Datatypes.length stk1 = frame ->
    forall x',
      args_stack_sem args fenv (stk1 ++ x') (stk1 ++ x', vals).

Lemma stack_mutated_at_index_app :
  forall (stk1 stk2 x: stack) (k: stack_index) (c: nat),
    k <= Datatypes.length stk1 ->
    stack_mutated_at_index (stk2 ++ x) k c (stk1 ++ x) ->
    forall x',
      stack_mutated_at_index (stk2 ++ x') k c (stk1 ++ x').
Proof.
  induction stk1; intros.
  - simpl in H. invs H.
    invs H0.
    invs H2.
  - pose proof (H0' := H0).
    apply stack_mutated_at_index_preserves_length in H0.
    repeat rewrite app_length in H0. apply addition_elimination in H0.
    destruct stk2; [ simpl in H0; invs H0 | ].
    invs H0'.
    + simpl. econstructor.
      apply app_decomposition in H5. destruct H5. subst. reflexivity.
      simpl in H0. invs H0. reflexivity.
    + simpl. econstructor. assumption.
      rewrite app_length in *.
      simpl in H. rewrite app_length in H9.
      apply addition_elimination in H9. rewrite <- H9 in H.
      lia.
      repeat rewrite app_length.
      repeat rewrite app_length in H9.
      apply addition_elimination in H9. rewrite H9. reflexivity.
      eapply IHstk1.
      simpl in H. lia.
      eassumption.
      reflexivity.
Qed.

Lemma aexp_frame_pure_mut_stronger :
  stack_sem_mut_ind_theorem  P_aexp_frame_pure_mut P0_aexp_frame_pure_mut P1_aexp_frame_pure_mut P2_aexp_frame_pure_mut.
Proof.
  stack_sem_mutual_induction P P0 P1 P2 P_aexp_frame_pure_mut P0_aexp_frame_pure_mut P1_aexp_frame_pure_mut P2_aexp_frame_pure_mut; intros.
  - rewrite H1 in H0.
    invs H.
    eapply app_decomposition in H0; [ | symmetry in H7; assumption].
    destruct H0. subst.
    econstructor.
  - invs H0.
    simplify_stacks. eapply H with (stk1 := stk1) (x := x) (v := c) (stk' := stk1 ++ x) (x' := x') in H12. apply stack_mutated_at_index_app with (x' := x') in s.
    econstructor.
    assumption. rewrite app_length. rewrite H11. lia.
    eassumption.
    assumption.
    rewrite <- H11 in H8. assumption.
    reflexivity. reflexivity. reflexivity. assumption.
  - invs H.
    rewrite app_comm_cons in H1. apply app_inv_tail in H1. rewrite <- H1. simpl. econstructor.
    reflexivity.
  - invs H. rewrite app_comm_cons in H0. apply app_inv_tail in H0. rewrite <- H0. simpl. econstructor.
    eauto.
  - invs H1.
    eapply imp_frame_rule_length with (frame := Datatypes.length stk1) in i; [ | eassumption | .. ]. destruct_exists.
    eapply imp_frame_rule_length with (frame := frame'0) in i0; [ | eassumption | .. ]. destruct_exists.
    econstructor.
    eapply H. eassumption. eauto.
    apply app_decomposition in A1. destruct A1. rewrite H3 in i. symmetry in i. eapply i. assumption.
    reflexivity.
    assumption.
    eapply H0. eassumption.
    apply app_decomposition in A1. destruct A1. rewrite H3 in i. symmetry in i. eapply i. assumption. reflexivity. assumption.
    reflexivity.
    rewrite <- i. rewrite app_length. rewrite A0. lia.
    rewrite app_length. lia.
  - invs H1.
    econstructor. eapply H. eassumption. eauto. eauto. simplify_stacks. reflexivity.
    reflexivity. eapply H0. eassumption. simplify_stacks. reflexivity. reflexivity. reflexivity. reflexivity.
  - invs H1. eapply Stack_if_false.
    eapply H. eassumption. eauto. eauto. simplify_stacks. reflexivity.
    reflexivity. eapply H0. eassumption. simplify_stacks. reflexivity. reflexivity. reflexivity. reflexivity.
  - invs H0. econstructor.
    match goal with
  | [ H: aexp_frame_rule ?a ?fenv _,
        H': aexp_stack_sem ?a ?fenv ?stk (?stk', _) |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk = stk') by (eapply aexp_frame_implies_pure; eassumption);
      rewrite <- same in *; clear same
  | [ H: bexp_frame_rule ?b ?fenv _,
        H': bexp_stack_sem ?b ?fenv ?stk (?stk', _) |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk = stk') by (eapply bexp_frame_implies_pure; eassumption);
      rewrite <- same in *
  | [ H: args_frame_rule ?args ?fenv _,
        H' : args_stack_sem ?args ?fenv ?stk (?stk', _) |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk = stk') by (eapply args_frame_implies_pure; eassumption);
      rewrite <- same in *; clear same
    end.
    apply app_decomposition' in SAME.
    destruct SAME. rewrite H1. eapply H; eauto. rewrite H1. eauto. rewrite H1. eauto. auto.
  - invs H2. simplify_stacks.
    eapply imp_frame_rule_length with (frame := Datatypes.length stk4) in i0; [ | eassumption | .. ]. destruct_exists.
    apply app_decomposition in A1. destruct A1.
    rewrite H4 in i0. symmetry in i0.
    eapply Stack_while_step. eapply H.
    eassumption. eauto. eauto. reflexivity. assumption.
    eapply H0. eassumption. eauto. eauto. assumption. assumption.
    eapply H1. eassumption. eassumption. reflexivity. rewrite A0. symmetry. auto. reflexivity. rewrite H12. assumption.
    rewrite app_length. rewrite H12. lia.
  - invs H0. econstructor.
  - invs H. econstructor. assumption. rewrite app_length. lia.
    erewrite nth_error_app1.
    erewrite nth_error_app1 in e. invs H0. assumption. lia. lia.
  - invs H2. invs H1.
    econstructor.
    + eapply H. eassumption. eauto. eauto. simplify_stacks. reflexivity. reflexivity.
    + eapply H0. eassumption. eauto. simplify_stacks. reflexivity. reflexivity. reflexivity.
  - invs H2. invs H1.
    econstructor.
    + eapply H. eassumption. eauto. eauto. simplify_stacks. reflexivity. reflexivity.
    + eapply H0. eassumption. eauto. simplify_stacks. reflexivity. reflexivity. reflexivity.
  - subst. invs H3. clear H3. invs H2. assert (stk0 ++ x = stk1).
    eapply args_frame_implies_pure. eassumption. eassumption.
    symmetry in H3. subst.
    simplify_stacks.
    eapply imp_frame_rule_length in i; [ | eassumption | .. ].
    destruct_exists. symmetry in i. apply app_decomposition in A1.
    destruct A1.
    subst.
    econstructor.
    eauto. eauto. eauto. eauto. reflexivity.
    eapply H. eassumption. eauto. reflexivity.
    reflexivity. reflexivity. eapply H0. eassumption.
    eauto. eauto. rewrite e3. eapply args_stack_sem_preserves_length in a. rewrite A. rewrite e3. reflexivity.
    assumption.
    eapply H1. eassumption. eauto. eauto. reflexivity. assumption.
    eapply same_after_popping_length1.
    rewrite <- e3. assumption.
    reflexivity.
    rewrite A. rewrite e3. eapply args_stack_sem_preserves_length in a. assumption.
    rewrite app_length. eapply args_stack_sem_preserves_length in a. rewrite <- a. rewrite <- e3. lia.
  - invs H. invs H0. econstructor.
  - invs H0. econstructor.
  - invs H0. invs H1. econstructor. eapply H. eassumption. eauto. eauto. reflexivity. reflexivity. reflexivity.
  - invs H2. invs H1. simplify_stacks'.
    econstructor.
    + eapply H. eassumption. eauto. eauto. reflexivity. reflexivity.
    + eapply H0. eassumption. eauto. eauto. reflexivity. reflexivity.
    + reflexivity.
  - invs H2. invs H1. simplify_stacks'.
    econstructor.
    + eapply H. eassumption. eauto. eauto. reflexivity. reflexivity.
    + eapply H0. eassumption. eauto. eauto. reflexivity. reflexivity.
    + reflexivity.
  - invs H2. invs H1. simplify_stacks'.
    econstructor.
    + eapply H. eassumption. eauto. eauto. reflexivity. reflexivity.
    + eapply H0. eassumption. eauto. eauto. reflexivity. reflexivity.
    + reflexivity.
  - invs H2. invs H1. simplify_stacks'.
    econstructor.
    + eapply H. eassumption. eauto. eauto. reflexivity. reflexivity.
    + eapply H0. eassumption. eauto. eauto. reflexivity. reflexivity.
    + reflexivity.
  - invs H0. econstructor.
  - invs H2. invs H1. simplify_stacks.
    econstructor.
    + eapply H. eassumption. eauto. eauto. reflexivity. reflexivity.
    + eapply H0. eassumption. eauto. eauto. reflexivity. reflexivity.
Qed.

Lemma aexp_frame_pure_mut:
   (forall (aexp : aexp_stack) (fenv : fun_env_stk) (frame : nat),
     aexp_frame_rule aexp fenv frame ->
     forall x stk stk' aexpval,
       frame = Datatypes.length x ->
       aexp_stack_sem aexp fenv (x ++ stk) (x ++ stk, aexpval) ->
       aexp_stack_sem aexp fenv (x ++ stk') (x ++ stk', aexpval)) /\
   (forall (args: list aexp_stack) (fenv: fun_env_stk) (frame: nat),
     args_frame_rule args fenv frame ->
     forall x stk stk' aexpvals,
       frame = Datatypes.length x ->
       args_stack_sem args fenv (x ++ stk) (x ++ stk, aexpvals) ->
       args_stack_sem args fenv (x ++ stk') (x ++ stk', aexpvals)) /\
   (forall (b: bexp_stack) (fenv: fun_env_stk) (frame: nat),
     bexp_frame_rule b fenv frame ->
     forall x stk stk' bexpval,
       frame = Datatypes.length x ->
       bexp_stack_sem b fenv (x ++ stk) (x ++ stk, bexpval) ->
       bexp_stack_sem b fenv (x ++ stk') (x ++ stk', bexpval)) /\
   (forall (i: imp_stack) (fenv: fun_env_stk) (frame frame': nat),
     imp_frame_rule i fenv frame frame' ->
     forall x x' stk stk',
       frame = Datatypes.length x ->
       frame' = Datatypes.length x' ->
       imp_stack_sem i fenv (x ++ stk) (x' ++ stk) ->
       imp_stack_sem i fenv (x ++ stk') (x' ++ stk')).
Proof.
  pose proof (aexp_frame_pure_mut_stronger).
  unfold stack_sem_mut_ind_theorem in H.
  destruct_exists_helper H.
  split_helper; intros.
  - eapply A0.
    eassumption.
    eassumption.
    eauto. eauto. reflexivity. symmetry. auto.
  - eapply H; eauto.
  - eapply A1; eauto.
  - eapply A; eauto.
Qed.

Lemma frame_preserves_rest_stk :
  forall vals stk stk' inner_stk i fenv,
    imp_frame_rule i fenv (Datatypes.length vals) (Datatypes.length inner_stk) ->
    imp_stack_sem i fenv (vals ++ stk) (inner_stk ++ stk) ->
    imp_stack_sem i fenv (vals ++ stk') (inner_stk ++ stk').
Proof.
  destruct aexp_frame_pure_mut as (_ & _ & _ & IMP).
  intros.
  eapply IMP; eauto.
Qed.

Lemma aexp_frame_pure :
  forall x stk stk' aexp aexpval fenv,
    aexp_stack_sem aexp fenv (x ++ stk) (x ++ stk, aexpval) ->
    aexp_frame_rule aexp fenv (Datatypes.length x) ->
    aexp_stack_sem aexp fenv (x ++ stk') (x ++ stk', aexpval).
Proof.
  intros. destruct aexp_frame_pure_mut. eapply H1; eauto.
Qed.


Lemma bexp_frame_pure :
  forall (b: bexp_stack) (fenv: fun_env_stk) (frame: nat),
    bexp_frame_rule b fenv frame ->
    forall x stk stk' bexpval,
      frame = Datatypes.length x ->
      bexp_stack_sem b fenv (x ++ stk) (x ++ stk, bexpval) ->
      bexp_stack_sem b fenv (x ++ stk') (x ++ stk', bexpval).
Proof.
  intros. eapply aexp_frame_pure_mut; eauto.
Qed.


