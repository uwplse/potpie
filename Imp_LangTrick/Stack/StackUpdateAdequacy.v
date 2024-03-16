From Coq Require Import List Arith Bool String.

From Imp_LangTrick Require Import StackLanguage StackLogicBase Base StackLangTheorems LogicProp.

Lemma arith_update_adequacy_forwards :
  forall k newval a a',
    arith_update k newval a = a' ->
    arith_update_rel k newval a a'.
Proof.
  intros k newval. intros a.
  eapply aexp_stack_ind2 with (P := fun a => forall a', arith_update k newval a = a' -> arith_update_rel k newval a a'); intros.
  - simpl in H. rewrite <- H. econstructor.
  - simpl in H. destruct (k =? n) eqn:Heq.
    + eapply EqNat.beq_nat_true_stt in Heq.
      rewrite Heq. rewrite H. econstructor. reflexivity.
    + eapply EqNat.beq_nat_false_stt in Heq.
      rewrite <- H.
      eapply UpVarStkNoMatch. assumption.
  - simpl in H1. rewrite <- H1. econstructor.
    + eapply H. reflexivity.
    + eapply H0. reflexivity.
  - simpl in H1. rewrite <- H1. econstructor; [ eapply H | eapply H0 ]; reflexivity.
  - rewrite <- H0. simpl. econstructor. revert H. clear H0. induction aexps; intros.
    + simpl. econstructor.
    + invs H. simpl. econstructor.
      * eapply H2. reflexivity.
      * eapply IHaexps. assumption.
Qed.

Lemma arith_update_adequacy_backwards :
  forall k newval a a',
    arith_update_rel k newval a a' ->
    arith_update k newval a = a'.
Proof.
  intros k newval a.
  eapply aexp_stack_ind2 with (P := fun a => forall a', arith_update_rel k newval a a' -> arith_update k newval a = a'); intros;
    match goal with
    | [ H: arith_update_rel _ _ _ _ |- _ ] => invs H
    end.
  - simpl. reflexivity.
  - simpl. rewrite <- EqNat.beq_nat_refl_stt. reflexivity.
  - simpl. eapply Nat.eqb_neq in H3. rewrite H3. reflexivity.
  - eapply H in H6. eapply H0 in H8. rewrite <- H6, <- H8. simpl. reflexivity.
  - eapply H in H6. eapply H0 in H8. rewrite <- H6, <- H8. reflexivity.
  - simpl. f_equal. revert H6. clear H0. revert args'. revert H. induction aexps; intros.
    + invs H6. simpl. reflexivity.
    + invs H6. simpl. invs H. eapply H2 in H4. rewrite <- H4. f_equal. eapply IHaexps. eassumption. eassumption.
Qed.

Lemma bool_update_adequacy_forwards :
  forall k newval b b',
    bool_update k newval b = b' ->
    bool_update_rel k newval b b'.
Proof.
  induction b; intros;
    match goal with
    | [ H: bool_update _ _ _ = _ |- _ ] => simpl in H
    end.
  - rewrite <- H. econstructor.
  - rewrite <- H. econstructor.
  - rewrite <- H. econstructor. eapply IHb. reflexivity.
  - rewrite <- H. econstructor; [ eapply IHb1 | eapply IHb2 ]; reflexivity.
  - rewrite <- H. econstructor; [ eapply IHb1 | eapply IHb2 ]; reflexivity.
  - rewrite <- H. econstructor; eapply arith_update_adequacy_forwards; reflexivity.
  - rewrite <- H. econstructor; eapply arith_update_adequacy_forwards; reflexivity.
Qed.

Lemma bool_update_adequacy_backwards :
  forall k newval b b',
    bool_update_rel k newval b b' ->
    bool_update k newval b = b'.
Proof.
  induction b; intros;
    match goal with
    | [ H: bool_update_rel _ _ _ _ |- _ ] => invs H
    end; simpl.
  - reflexivity.
  - reflexivity.
  - eapply IHb in H3. rewrite <- H3. reflexivity.
  - eapply IHb1 in H4. eapply IHb2 in H6. rewrite <- H4, <-H6. reflexivity.
  - eapply IHb1 in H4. eapply IHb2 in H6. rewrite <- H4, <- H6. reflexivity.
  - eapply arith_update_adequacy_backwards in H4. eapply arith_update_adequacy_backwards in H6. rewrite <- H4, <- H6. reflexivity.
  - eapply arith_update_adequacy_backwards in H4. eapply arith_update_adequacy_backwards in H6. rewrite <- H4, <- H6. reflexivity.
Qed.

Lemma lp_bool_update_adequacy_forwards :
  forall k newval (lp lp': LogicProp bool bexp_stack),
    transform_prop_exprs lp (bool_update k newval) = lp' ->
    transformed_prop_exprs (bool_update_rel k newval) lp lp'.
Proof.
  induction lp; intros;
    match goal with
    | [ H : transform_prop_exprs _ _ = _ |- _ ] =>
        simpl in H; rewrite <- H
    end.
  - econstructor.
  - econstructor.
  - econstructor. eapply bool_update_adequacy_forwards. reflexivity.
  - econstructor; eapply bool_update_adequacy_forwards; reflexivity.
  - econstructor; [eapply IHlp1 | eapply IHlp2]; reflexivity.
  - econstructor; [eapply IHlp1 | eapply IHlp2]; reflexivity.
  - econstructor; eapply bool_update_adequacy_forwards; reflexivity.
  - econstructor. clear H. clear lp'. induction a_list.
    + econstructor.
    + simpl. econstructor. eapply bool_update_adequacy_forwards. reflexivity. eapply IHa_list.
Qed.

Lemma lp_bool_update_adequacy_backwards :
  forall k newval (lp lp': LogicProp bool bexp_stack),
    transformed_prop_exprs (bool_update_rel k newval) lp lp' ->
    transform_prop_exprs lp (bool_update k newval) = lp'.
Proof.
  induction lp; intros;
    match goal with
    | [ H: transformed_prop_exprs _ _ _ |- _ ] =>
        invs H
    end;
    simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. eapply bool_update_adequacy_backwards. assumption.
  - f_equal; eapply bool_update_adequacy_backwards; eassumption.
  - f_equal; [eapply IHlp1 | eapply IHlp2]; eassumption.
  - f_equal; [eapply IHlp1 | eapply IHlp2]; eassumption.
  - f_equal; eapply bool_update_adequacy_backwards; eassumption.
  - f_equal. clear H. revert H4. revert a_list'. induction a_list; intros.
    + invs H4. reflexivity.
    + invs H4. simpl. f_equal.
      * eapply bool_update_adequacy_backwards. assumption.
      * eapply IHa_list. eassumption.
Qed.

Lemma lp_arith_update_adequacy_forwards :
  forall k newval (lp lp': LogicProp nat aexp_stack),
    transform_prop_exprs lp (arith_update k newval) = lp' ->
    transformed_prop_exprs (arith_update_rel k newval) lp lp'.
Proof.
  induction lp; intros;
    match goal with
    | [ H: transform_prop_exprs _ _ = _ |- _ ] =>
        simpl in H; rewrite <- H
    end; econstructor.
  - eapply arith_update_adequacy_forwards. reflexivity.
  - eapply arith_update_adequacy_forwards. reflexivity.
  - eapply arith_update_adequacy_forwards; reflexivity.
  - eapply IHlp1. reflexivity.
  - eapply IHlp2. reflexivity.
  - eapply IHlp1. reflexivity.
  - eapply IHlp2. reflexivity.
  - eapply arith_update_adequacy_forwards. reflexivity.
  - eapply arith_update_adequacy_forwards; reflexivity.
  - eapply arith_update_adequacy_forwards. reflexivity.
  - clear H. clear lp'. induction a_list.
    + econstructor.
    + simpl. econstructor.
      * eapply arith_update_adequacy_forwards. reflexivity.
      * eapply IHa_list.
Qed.

Lemma lp_arith_update_adequacy_backwards :
  forall k newval (lp lp': LogicProp nat aexp_stack),
    transformed_prop_exprs (arith_update_rel k newval) lp lp' ->
    transform_prop_exprs lp (arith_update k newval) = lp'.
Proof.
  induction lp; intros;
    match goal with
    | [ H : transformed_prop_exprs _ _ _ |- _ ] =>
        invs H; simpl
    end.
  - reflexivity.
  - reflexivity.
  - f_equal. eapply arith_update_adequacy_backwards. assumption.
  - f_equal; eapply arith_update_adequacy_backwards; assumption.
  - f_equal; [ eapply IHlp1 | eapply IHlp2 ]; eassumption.
  - f_equal; [ eapply IHlp1 | eapply IHlp2 ]; eassumption.
  - f_equal; eapply arith_update_adequacy_backwards; assumption.
  - f_equal. clear H. revert H4. revert a_list'. induction a_list; intros.
    + invs H4. reflexivity.
    + invs H4. simpl. f_equal.
      * eapply arith_update_adequacy_backwards. assumption.
      * eapply IHa_list. assumption.
Qed.

Lemma meta_update_adequacy_forwards :
  forall k newval mp1 mp2,
    meta_update k newval mp1 = mp2 ->
    meta_update_rel k newval mp1 mp2.
Proof.
  induction mp1; intros.
  - rewrite <- H. econstructor. eapply lp_bool_update_adequacy_forwards. reflexivity.
  - rewrite <- H. econstructor. eapply lp_arith_update_adequacy_forwards. reflexivity.
Qed.

Lemma meta_update_adequacy_backwards :
  forall k newval mp1 mp2,
    meta_update_rel k newval mp1 mp2 ->
    meta_update k newval mp1 = mp2.
Proof.
  induction mp1; intros.
  - invs H. simpl. f_equal. eapply lp_bool_update_adequacy_backwards. assumption.
  - invs H. simpl. f_equal. eapply lp_arith_update_adequacy_backwards. assumption.
Qed.

Inductive stack_large_enough_for_state : stack_index -> AbsState -> Prop :=
| LargeEnoughBase :
  forall k s m,
    stack_large_enough k s ->
    stack_large_enough_for_state k (BaseState s m)
| LargeEnoughAnd :
  forall k s1 s2,
    stack_large_enough_for_state k s1 ->
    stack_large_enough_for_state k s2 ->
    stack_large_enough_for_state k (AbsAnd s1 s2)
| LargeEnoughOr :
  forall k s1 s2,
    stack_large_enough_for_state k s1 ->
    stack_large_enough_for_state k s2 ->
    stack_large_enough_for_state k (AbsOr s1 s2).


Lemma state_update_adequacy_forwards :
  forall k newval s1 s2,
    StackExprWellFormed.aexp_well_formed newval ->
    StackExprWellFormed.absstate_well_formed s1 ->
    stack_large_enough_for_state k s1 ->
    state_update k newval s1 = s2 ->
    state_update_rel k newval s1 s2.
Proof.
  induction s1; intros.
  - rewrite <- H2. econstructor.
    + eapply meta_update_adequacy_forwards. reflexivity.
    + assumption.
    + invs H0. eassumption.
    + invs H1. assumption.
  - rewrite <- H2. simpl. invs H0. invs H1. econstructor.
    + eapply IHs1_1.
      * assumption.
      * eassumption.
      * assumption.
      * reflexivity.
    + eapply IHs1_2; try assumption; try reflexivity.
    + eassumption.
    + eassumption.
    + eassumption.
  - rewrite <- H2. simpl. invs H0. invs H1. econstructor.
    + eapply IHs1_1; try assumption; try reflexivity.
    + eapply IHs1_2; try assumption; try reflexivity.
    + eassumption.
    + eassumption.
    + eassumption.
Qed.

Lemma state_update_adequacy_backwards :
  forall k newval s1 s2,
    StackExprWellFormed.aexp_well_formed newval ->
    StackExprWellFormed.absstate_well_formed s1 ->
    stack_large_enough_for_state k s1 ->
    state_update_rel k newval s1 s2 ->
    state_update k newval s1 = s2.
Proof.
  induction s1; intros.
  - invs H2. simpl. f_equal. eapply meta_update_adequacy_backwards. assumption.
  - invs H2. simpl. f_equal.
    + eapply IHs1_1. eassumption. eassumption. invs H1. eassumption. eassumption.
    + eapply IHs1_2. eassumption. eassumption. invs H1. eassumption. eassumption.
  - invs H2. simpl. f_equal.
    + eapply IHs1_1. eassumption. eassumption. invs H1. eassumption. eassumption.
    + eapply IHs1_2. eassumption. eassumption. invs H1. eassumption. eassumption.
Qed.
        
      
      
  (* UpVarStkNoMatch *)
