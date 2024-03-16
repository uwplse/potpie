From Coq Require Import Arith Psatz Bool String List Nat Program.Equality.

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

From Imp_LangTrick Require Import Stack.StackLanguage LogicProp Stack.StackLogicBase Stack.StackFrame Stack.StackPurest
        Stack.StackExprWellFormed.

Lemma index_greater_than_one :
  forall (stk: stack) k n,
    1 <= k ->
    k <= List.length (n :: stk) ->
    exists stk',
      n :: stk' = firstn k (n :: stk).
Proof.
  destruct k; intros.
  - inversion H.
  - exists (firstn k stk). reflexivity.
Qed.

Lemma index_replacement :
  forall (stk stk': stack) (k: stack_index) (n: nat),
    1 <= k ->
    k <= List.length stk ->
    stack_mutated_at_index stk' k n stk ->
    stk' = (firstn (k - 1) stk ++ n :: skipn k stk).
Proof.
  destruct k.
  - intros. invs H.
  - revert stk' k. induction stk; intros; invs H1; auto.
    rewrite skipn_cons. destruct k.
    + invs H4. invs H3.
    + replace (S (S k) - 1) with (S (S k - 1)) by lia. rewrite firstn_cons. 
      remember (S k) as k'. simpl. f_equal. subst.
      eapply IHstk; eauto; try lia.
Qed.  

Lemma stack_mutation_preserves_length :
  forall (stk stk': stack) (k: stack_index) (n: nat),
    1 <= k ->
    k <= List.length stk ->
    stack_mutated_at_index stk' k n stk ->
    List.length stk = List.length stk'.
Proof.
  induction k; intros; invs H1; auto.
  - inversion H2.
  - simpl. f_equal. auto. 
Qed.

Definition index_in_stack (k: stack_index) (stk: stack): Prop :=
  1 <= k /\ k <= List.length stk.

Definition nth_error_1_indexed (stk: stack) (k: stack_index): option nat :=
  nth_error stk (k - 1).

Lemma stack_mutation_other_indices_help :
  forall (stk stk': stack) (k: nat) (n n': nat) (k': nat),
    stack_mutated_at_index stk' (k + 1) n stk ->
    k <> k' ->
    k < List.length stk ->
    k' < List.length stk ->
    nth_error stk k' = Some n' ->
    nth_error stk' k' = Some n'.
Proof.
  intros stk stk' k n n' k' MUTATE NEQ IN_STK_k IN_STK_k' NTH.
  revert NTH IN_STK_k' IN_STK_k NEQ. revert n' k'.
  dependent induction MUTATE; intros.
  - destruct k; [ | inversion x; rewrite Nat.add_comm in H1; inversion H1].
    destruct k'.
    + contradiction. 
    + subst. auto.
  - destruct k'.
    + auto.
    + simpl.
      assert (exists k'', k = S k'') by (destruct k; [simpl in H; inversion H; inversion H3 | ]; exists k; reflexivity).
      destruct H2.
      apply IHMUTATE with (k := x) (n' := n'0); simpl in *; auto; try lia.
      replace (k + 1 - 1) with k by lia.
      replace (x + 1) with (S x) by lia.
      rewrite <- H2. apply JMeq_refl.
Qed.

Lemma exists_successor :
  forall (n: nat),
    1 <= n ->
    exists n',
      n = S n'.
Proof.
  induction 1; eauto.
Qed.

Lemma plus_one_is_successor :
  forall (n: nat),
    n + 1 = S n.
Proof.
  intros n. lia.
Qed.

Lemma stack_mutation_other_indices_invariant :
  forall (stk stk': stack) (k: stack_index) (n n': nat) (k': stack_index),
    stack_mutated_at_index stk' k n stk ->
    k <> k' ->
    index_in_stack k stk ->
    index_in_stack k' stk ->
    nth_error_1_indexed stk k' = Some n' ->
    nth_error_1_indexed stk' k' = Some n'.
Proof.
  intros stk stk' k n n' k' MUTATE NEQ IN_STK_k IN_STK_k' NTH.
  unfold nth_error_1_indexed in *.
  unfold index_in_stack in *.
  destruct IN_STK_k.
  assert (exists k'', k = S k'') by (eapply exists_successor; eassumption).
  destruct H1.
  eapply stack_mutation_other_indices_help.
  - rewrite H1 in MUTATE. rewrite <- plus_one_is_successor in MUTATE. eassumption.
  - unfold not in *. intros. rewrite H2 in H1. rewrite <- Nat.sub_succ_l in H1; [ | intuition].
    rewrite successor_minus_one_same in H1. apply NEQ in H1. assumption.
  - rewrite H1 in H0. intuition.
  - intuition.
  - assumption.
Qed.


Lemma nth_error_of_mutated_stack :
  forall n stk stk' val,
    stack_mutated_at_index stk' (S n) val stk ->
    nth_error stk' n = Some val.
Proof.
  induction n; intros; invs H; auto.
  - inversion H0. inversion H5.
  - replace (S (S n) - 1) with (S n) in H3 by reflexivity.
    eapply IHn. eassumption.
Qed.


Ltac aexp_det aexp :=
  match goal with
  | [ H1 : aexp_stack_sem aexp ?fenv ?stk1 (?stk1, ?n1), H2 : aexp_stack_sem aexp ?fenv ?stk2 (?stk2, ?n2) |- _ ] =>
      let same := fresh "SAME" in
      assert (same : (stk1, n1) = (stk2, n2)) by (eapply aexp_stack_sem_det; eassumption);
      invs same
  end.

Ltac aexp_pure aexp :=
  match goal with
  | [ H1 : aexp_stack_sem aexp ?fenv ?stk1 (?stk2, ?n), H2: aexp_stack_pure_rel aexp ?fenv |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk1 = stk2) by (eapply aexp_stack_pure_backwards in H2; eapply H2; eassumption);
      subst
  end.

Ltac args_pure args :=
  match goal with
  | [ H1 : args_stack_sem args ?fenv ?stk1 (?stk2, ?vals), H2: args_stack_pure_rel args ?fenv |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk1 = stk2) by (eapply args_stack_pure_implication with (stk := stk1) (stk' := stk2) in H2; eassumption)
  end.

Ltac bexp_pure bexp :=
  match goal with
  | [ H1 : bexp_stack_sem bexp ?fenv ?stk1 (?stk2, ?n), H2: bexp_stack_pure_rel bexp ?fenv |- _ ] =>
      let same := fresh "SAME" in
      assert (same: stk1 = stk2) by (eapply bexp_stack_pure_implication in H2; eapply H2; eassumption);
      subst
  end.



Lemma arith_substitution_preserves_purity :
  forall k a aexp aexp',
    arith_update_rel k a aexp aexp' ->
    forall fenv,
      aexp_stack_pure_rel a fenv ->
      aexp_stack_pure_rel aexp fenv ->
      aexp_stack_pure_rel aexp' fenv.
Proof.
  apply
   (arith_update_rel_mut
     (fun k a aexp aexp' H =>
       forall fenv,
         aexp_stack_pure_rel a fenv ->
         aexp_stack_pure_rel aexp fenv ->
         aexp_stack_pure_rel aexp' fenv)
     (fun k a args args' H =>
        forall fenv,
          aexp_stack_pure_rel a fenv ->
          args_stack_pure_rel args fenv ->
          args_stack_pure_rel args' fenv)); intros; auto.
  - invs H2. econstructor; eauto.
  - invs H2. econstructor; eauto.
  - invs H1. econstructor; eauto.
  - invs H2. econstructor; eauto.
Qed.

Check args_update_rel_mut.

Lemma args_substitution_preserves_purity :
  forall k a args args',
    args_update_rel k a args args' ->
    forall fenv,
      aexp_stack_pure_rel a fenv ->
      args_stack_pure_rel args fenv ->
      args_stack_pure_rel args' fenv.
Proof.
  apply
   (args_update_rel_mut
     (fun k a aexp aexp' H =>
       forall fenv,
         aexp_stack_pure_rel a fenv ->
         aexp_stack_pure_rel aexp fenv ->
         aexp_stack_pure_rel aexp' fenv)
     (fun k a args args' H =>
        forall fenv,
          aexp_stack_pure_rel a fenv ->
          args_stack_pure_rel args fenv ->
          args_stack_pure_rel args' fenv)); intros; auto.
  - invs H2. econstructor; eauto.
  - invs H2. econstructor; eauto.
  - invs H1. econstructor; eauto.
  - invs H2. econstructor; eauto.
Qed.

Lemma bool_substitution_preserves_purity :
  forall b b' k a fenv,
    bool_update_rel k a b b' ->
    aexp_stack_pure_rel a fenv ->
    bexp_stack_pure_rel b fenv ->
    bexp_stack_pure_rel b' fenv.
Proof.
  intros b b' k a fenv H. revert fenv.
  induction H; intros; eauto.
  - invs H1. econstructor; eauto.
  - invs H2. econstructor; eauto.
  - invs H2. econstructor; eauto.
  - invs H2. 
    econstructor; eauto; eapply arith_substitution_preserves_purity; eauto.
  - invs H2. econstructor; eauto; eapply arith_substitution_preserves_purity; eauto.
Qed.

Definition arith_args_substitution_vs_update_P (k: stack_index) (a: aexp_stack) (aexp aexp': aexp_stack): Prop :=
  forall aval aexpval fenv stk stk',
    aexp_stack_pure_rel a fenv ->
    aexp_stack_pure_rel aexp fenv ->
    aexp_stack_sem a fenv stk (stk, aval) ->
    stack_mutated_at_index stk' k aval stk ->
    aexp_stack_sem aexp' fenv stk (stk, aexpval)  ->
    aexp_stack_sem aexp fenv stk' (stk', aexpval).

Definition arith_args_substitution_vs_update_P0 (k: stack_index) (a: aexp_stack) (args args': list aexp_stack): Prop :=
  forall aval argsvals fenv stk stk',
    aexp_stack_pure_rel a fenv ->
    args_stack_pure_rel args fenv ->
    aexp_stack_sem a fenv stk (stk, aval) ->
    stack_mutated_at_index stk' k aval stk ->
    args_stack_sem args' fenv stk (stk, argsvals) ->
    args_stack_sem args fenv stk' (stk', argsvals).

Ltac arith_sub_pure a1' :=
  match goal with
  | [ H : aexp_stack_pure_rel a1' ?fenv' |- _ ] => idtac "found stack pure"
  | [ H2 : arith_update_rel ?k ?a ?a1 a1', H1 : aexp_stack_pure_rel ?a1'' ?fenv'  |- _ ] =>  eapply arith_substitution_preserves_purity with (fenv := fenv') in H2
  end;
  [ match goal with
    | [ H' : aexp_stack_pure_rel a1' ?fenv' |- _ ] =>
        eapply aexp_stack_pure_backwards in H';
        unfold aexp_stack_pure in H';
        match goal with
        | [ H3 : aexp_stack_sem a1' ?fenv ?stk1 (?stk2, ?n) |- _ ] =>
            let copy := fresh "H3" in
            pose proof (copy := H3); eapply H' in copy; rewrite copy in *; clear copy
        end
                                    
    end | assumption .. ]
.

Ltac bool_sub_pure a1' :=
  match goal with
  | [ H : bexp_stack_pure_rel a1' ?fenv' |- _ ] => idtac "found stack pure"
  | [ H2 : bool_update_rel ?k ?a ?a1 a1', H1 : bexp_stack_pure_rel ?a1'' ?fenv'  |- _ ] =>  eapply bool_substitution_preserves_purity with (fenv := fenv') in H2
  end;
  [ match goal with
    | [ H' : bexp_stack_pure_rel a1' ?fenv' |- _ ] =>
        eapply bexp_stack_pure_implication in H';
        unfold bexp_stack_pure in H';
        match goal with
        | [ H3 : bexp_stack_sem a1' ?fenv ?stk1 (?stk2, ?n) |- _ ] =>
            let copy := fresh "H3" in
            pose proof (copy := H3); eapply H' in copy; rewrite copy in *; clear copy
        end
                                    
    end | assumption .. ].

Ltac args_sub_pure args' :=
  match goal with
  | [ H : args_stack_pure_rel args' ?fenv' |- _ ] => idtac "found stack pure"
  | [ H2 : args_update_rel ?k ?a ?a1 args', H1 : args_stack_pure_rel ?a1 ?fenv'  |- _ ] =>  idtac "found alternative"; eapply args_substitution_preserves_purity with (fenv := fenv') in H2
  end;
  [ match goal with
    | [ H' : args_stack_pure_rel args' ?fenv', H'' : args_stack_sem args' ?fenv ?stk1 (?stk2, ?n)  |- _ ] =>
        (eapply args_stack_pure_implication with (stk := stk1) (stk' := stk2) in H'; [ | eassumption ]);
        let copy := fresh "H3" in
        pose proof (copy := H''); rewrite <- H' in copy
    end | eassumption .. ].


Lemma args_update_preserves_length :
  forall (args args' : list aexp_stack) (k: stack_index) (a: aexp_stack),
    args_update_rel k a args args' ->
    Datatypes.length args = Datatypes.length args'.
Proof.
  intros args args' k a H. induction H; auto.
  simpl. f_equal. auto.
Qed.

Lemma same_after_popping_length :
  forall stk stk' n,
   Datatypes.length stk = n ->
   same_after_popping stk' (stk ++ stk') n.
Proof.
  induction stk; induction stk'; intros; subst; simpl; constructor; auto.
Qed.

Lemma arith_args_substitution_vs_update :
  (forall (k : stack_index) (a: aexp_stack) (aexp aexp' : aexp_stack),
      arith_update_rel k a aexp aexp' ->
      arith_args_substitution_vs_update_P k a aexp aexp') /\
    (forall (k : stack_index) (a : aexp_stack) (l l' : list aexp_stack),
        args_update_rel k a l l' ->
        arith_args_substitution_vs_update_P0 k a l l').
Proof.
  pose (fun (s: stack_index) (a a0 a1: aexp_stack) =>
        fun (_: arith_update_rel s a a0 a1) =>
          arith_args_substitution_vs_update_P s a a0 a1) as P.
  pose (fun (s: stack_index) (a: aexp_stack) (l l0: list aexp_stack) =>
        fun (_: args_update_rel s a l l0) =>
          arith_args_substitution_vs_update_P0 s a l l0) as P0.
  apply (expr_update_rel_mutind P P0); unfold P, P0; unfold arith_args_substitution_vs_update_P, arith_args_substitution_vs_update_P0; intros.
  - invs H3. econstructor.
  - invs H2.
    + constructor; auto.
      * simpl. lia.
      * simpl. f_equal. aexp_det a. auto.
    + constructor; try (simpl; lia).
      enough (exists k'', k' = S (S k'')).
      * destruct H8. subst. remember (S x) as k''.
        simpl. rewrite Nat.sub_0_r.
        simpl in H7. rewrite Nat.sub_0_r in H7. subst.
        simpl. aexp_det a.
        eapply nth_error_of_mutated_stack. eauto.
      * inversion H4.
        -- exists 0. reflexivity.
        -- inversion H8; eexists; eauto.
  - invs H3. inversion H2; eapply stack_mutation_other_indices_invariant with (stk := stk) (stk' := stk') (n' := aexpval) (n := aval) in n;
               unfold nth_error_1_indexed in n; try eassumption; unfold index_in_stack in *; try lia.
    + constructor; [ eassumption | .. ]; (subst; eassumption).
    + constructor; subst; try assumption. simpl. rewrite H8. assumption.
    + intuition. subst.
      rewrite H8 in H5. simpl. intuition.
  - invs H5. invs H2.
    econstructor.
    + eapply H; try eassumption.
      arith_sub_pure a1'. assumption.
    + eapply H0; try eassumption.
      arith_sub_pure a2'. assumption.
  - invs H5. invs H2.
    econstructor.
    + eapply H; try eassumption.
      arith_sub_pure a1'. assumption.
    + eapply H0; try eassumption.
      arith_sub_pure a2'. assumption.
  - inversion H4. revert H9 H10 H11 H12. invs H1. intros.
    rewrite Nat.add_comm in H20. pose proof (H22 := H20).
    eapply frame_implies_rest_stk_untouched_le with (stk := stk2) (stk1 := vals) (stk2 := stk1) in H20.
    destruct H20. destruct H6.
    econstructor.
    1-4: try eassumption.
    + symmetry. eapply args_update_preserves_length; eassumption.
    + eapply H; eauto.
      args_sub_pure args'.
      eassumption.
    + eapply frame_preserves_rest_stk.
      * rewrite <- H5 in * |- .
        rewrite H7 in * |- .
        rewrite <- H9 in * |- .
        rewrite <- H11 in * |- .
        rewrite <- H6 in H22.
        args_sub_pure args'. rewrite a0 in * |- .
        eapply args_stack_sem_preserves_length in H14.
        rewrite H10, H14, H9 in H22.
        eapply H22.
      * subst. eassumption.
    + pose proof (H13 := H12).
      eapply args_update_preserves_args_pure in a0; [ | eassumption .. ].
      args_sub_pure args'.
      rewrite a0 in * |- .
      rewrite H7 in * |- .
      rewrite <- H11.
      rewrite <- H9.
      rewrite <- H9 in H11.  rewrite <- H11 in H18.
      aexp_pure (Return_expr (fenv f)).
      eapply aexp_frame_pure.
      eassumption.
      rewrite H6. rewrite Nat.add_comm. assumption.
    + eapply H in H0; [ | eassumption .. | args_sub_pure args'; eassumption ].
      rewrite <- H11 in H18.
      rewrite <- H9 in H18.
      arith_sub_pure (Return_expr (fenv f)).
      eapply frame_implies_rest_stk_untouched_le in H22; [ | apply args_stack_sem_preserves_length in H14; rewrite H14 in H10; rewrite <- H9 in H10; eassumption | | subst; eassumption ].
      rewrite <- H9 in H10.
      rewrite <- H10.
      rewrite <- H9 in H5. rewrite <- H5.

      eapply same_after_popping_length.
      eassumption. subst.
      rewrite Nat.add_comm. rewrite <- H10 in H19.
      eapply same_after_popping_implies_geq_popped_length; eauto.
    + rewrite H9. eapply args_stack_sem_preserves_length in H14. rewrite H14 in H10. assumption.
    + subst. rewrite <- H10 in H19.
      pose proof (same_after_popping_implies_geq_popped_length stk stk3 _ H19).
      rewrite Nat.add_comm in H5. rewrite H5. 
      aexp_pure (Return_expr (fenv f)).
      eauto.
    + subst. assumption.
  - invs H3. econstructor.
  - invs H5.
    econstructor.
    + eapply H; eauto; invs H2; eauto.
      args_sub_pure args'.
      arith_sub_pure arg'.
      assumption.
    + eapply H0; eauto; invs H2; eauto.
      eapply arith_update_preserves_aexp_pure in a0; [ | eassumption | invs H2; assumption].
      arith_sub_pure arg'.
      assumption.
Qed.


Lemma arith_substitution_vs_update_folded :
  (forall (k : stack_index) (a: aexp_stack) (aexp aexp' : aexp_stack),
      arith_update_rel k a aexp aexp' ->
      arith_args_substitution_vs_update_P k a aexp aexp').
Proof.
  pose proof (arith_args_substitution_vs_update).
  destruct H. assumption.
Qed.

Lemma args_substitution_vs_update_folded :
  (forall (k : stack_index) (a : aexp_stack) (l l' : list aexp_stack),
      args_update_rel k a l l' ->
      arith_args_substitution_vs_update_P0 k a l l').
Proof.
  pose proof (arith_args_substitution_vs_update).
  destruct H. assumption.
Qed.

Lemma arith_substitution_vs_update :
  forall (k: stack_index) (a: aexp_stack) (aexp aexp': aexp_stack),
    arith_update_rel k a aexp aexp' ->
    forall aval aexpval fenv stk stk',
      aexp_stack_pure_rel a fenv ->
      aexp_stack_pure_rel aexp fenv ->
      aexp_stack_sem a fenv stk (stk, aval) ->
      stack_mutated_at_index stk' k aval stk ->
      aexp_stack_sem aexp' fenv stk (stk, aexpval)  ->
      aexp_stack_sem aexp fenv stk' (stk', aexpval).
Proof.
  pose proof (arith_substitution_vs_update_folded).
  unfold arith_args_substitution_vs_update_P in H.
  assumption.
Qed.

Lemma args_substitution_vs_update :
  forall (k: stack_index) (a: aexp_stack) (args args': list aexp_stack),
    args_update_rel k a args args' ->
    forall aval argsvals fenv stk stk',
      aexp_stack_pure_rel a fenv ->
      args_stack_pure_rel args fenv ->
      aexp_stack_sem a fenv stk (stk, aval) ->
      stack_mutated_at_index stk' k aval stk ->
      args_stack_sem args' fenv stk (stk, argsvals) ->
      args_stack_sem args fenv stk' (stk', argsvals).
Proof.
  pose proof (args_substitution_vs_update_folded).
  unfold arith_args_substitution_vs_update_P0 in H.
  assumption.
Qed.

Lemma bool_substitution_vs_update :
  forall (k: stack_index) (a: aexp_stack) (b b': bexp_stack),
    bool_update_rel k a b b' ->
    forall (aval: nat) (bval: bool) (fenv: fun_env_stk) (stk stk': stack),
      aexp_stack_pure_rel a fenv ->
      bexp_stack_pure_rel b fenv ->
      aexp_stack_sem a fenv stk (stk, aval) ->
      stack_mutated_at_index stk' k aval stk ->
      bexp_stack_sem b' fenv stk (stk, bval) ->
      bexp_stack_sem b fenv stk' (stk', bval).
Proof.
  intros ? ? ? ? UPDATE.
  dependent induction UPDATE; intros ? ? ? ? ? APURE BPURE AEXP MUTATE BEXP; invs BEXP.
  - constructor.
  - constructor.
  - econstructor; eauto.
    eapply IHUPDATE; try eassumption.
    invs BPURE. assumption.
  - invs BPURE. econstructor.
    + eapply IHUPDATE1; try eassumption.
      eapply bool_update_preserves_bexp_pure in UPDATE1; [ | eassumption .. ].
      bool_sub_pure b1'. eassumption.
    + eapply IHUPDATE2; [ eassumption .. | ].
      eapply bool_update_preserves_bexp_pure in UPDATE2; [ | eassumption .. ].
      bool_sub_pure b2'. eassumption.
    + reflexivity.
  - invs BPURE. econstructor.
    + eapply IHUPDATE1; [ eassumption .. | ].
      eapply bool_update_preserves_bexp_pure in UPDATE1; [ | eassumption ..].
      bool_sub_pure b1'.
      eassumption.
    + eapply IHUPDATE2; [eassumption .. | ].
      eapply bool_update_preserves_bexp_pure in UPDATE2; [ | eassumption ..].
      bool_sub_pure b2'. eassumption.
    + reflexivity.
  - invs BPURE. econstructor.
    + pose proof (A1PURE := H). eapply arith_update_preserves_aexp_pure in H; [ | eassumption .. ].
      eapply arith_substitution_vs_update; try eassumption.
      arith_sub_pure a1'. eassumption.
    + pose proof (A2PURE := H0). eapply arith_update_preserves_aexp_pure in H0; [ | eassumption .. ].
      eapply arith_substitution_vs_update; try eassumption.
      arith_sub_pure a2'. eassumption.
    + reflexivity.
  - invs BPURE. econstructor.
    + pose proof (A1PURE := H). eapply arith_update_preserves_aexp_pure in H; [ | eassumption .. ].
      eapply arith_substitution_vs_update; try eassumption.
      arith_sub_pure a1'. eassumption.
    + pose proof (A2PURE := H0). eapply arith_update_preserves_aexp_pure in H0; [ | eassumption .. ].
      eapply arith_substitution_vs_update; try eassumption.
      arith_sub_pure a2'. eassumption.
    + reflexivity.
Qed.

Lemma arith_update_implies_pure :
  forall k aval a a',
    arith_update_rel k aval a a' ->
    aexp_well_formed a ->
    forall fenv,
      aexp_stack_pure_rel aval fenv ->
      aexp_stack_pure_rel a' fenv ->
      aexp_stack_pure_rel a fenv.
Proof.
  apply
    (arith_update_rel_mut
       (fun k aval a a' (H : arith_update_rel k aval a a') =>
          aexp_well_formed a ->
          forall fenv,
            aexp_stack_pure_rel aval fenv ->
            aexp_stack_pure_rel a' fenv ->
            aexp_stack_pure_rel a fenv)
       (fun k aval args args' (H : args_update_rel k aval args args') =>
          args_well_formed args ->
          forall fenv,
            aexp_stack_pure_rel aval fenv ->
            args_stack_pure_rel args' fenv ->
            args_stack_pure_rel args fenv)); intros; auto.
  - econstructor; eauto. subst. invs H. auto.
  - invs H3. invs H1. econstructor; eauto. 
  - invs H3. invs H1. econstructor; eauto.
  - invs H2. invs H0. econstructor; eauto.
  - invs H3. invs H1. econstructor; eauto.
Qed.

Lemma bool_update_implies_pure :
  forall k aval b b',
    bool_update_rel k aval b b' ->
    bexp_well_formed b ->
    forall fenv,
      aexp_stack_pure_rel aval fenv ->
      bexp_stack_pure_rel b' fenv ->
      bexp_stack_pure_rel b fenv.
Proof.
  intros k aval b b' H. induction H; intros; auto; try solve [invs H2; invs H0; econstructor; eauto  | invs H3; invs H1; econstructor; eauto | invs H3; invs H1; econstructor; eauto; eapply arith_update_implies_pure; eauto ].
  (* - invs H2. invs H0. econstructor; eauto. *)
  (* - invs H3. invs H1. econstructor; eauto. *)
  (* - invs H3. invs H1. econstructor; eauto. *)
  (* - invs H3. invs H1. econstructor; eauto; eapply arith_update_implies_pure; eauto. *)
  (* - invs H3. invs H1. econstructor; eauto; eapply arith_update_implies_pure; eauto. *)
Qed.
  
Ltac bool_sub_update :=
  match goal with
  | [ |- bexp_stack_sem ?b' ?fenv ?stk (?stk, ?bval) ] =>
      match goal with
      | [ H: bool_update_rel ?k ?a ?b ?b' |- _ ] =>
          eapply bool_substitution_vs_update; try eassumption; eapply bool_update_implies_pure; eassumption
      | [ |- _ ] => idtac "no bool_update_rel found"
      end
  | [ |- _ ] =>
      idtac "no bexp_stack_sem goal found"
  end;
  try assumption;
  try eassumption.

Ltac arith_sub_update :=
  match goal with
  | [ |- aexp_stack_sem ?b' ?fenv ?stk (?stk, ?bval) ] =>
      match goal with
      | [ H: arith_update_rel ?k ?a ?b ?b' |- _ ] =>
          eapply arith_substitution_vs_update; try eassumption; eapply arith_update_implies_pure; eassumption
      | [ |- _ ] => idtac "no arith_update_rel found"
      end
  | [ |- _ ] =>
      idtac "no aexp_stack_sem goal found"
  end;
  try assumption;
  try eassumption.


Lemma eval_prop_args_rel_help :
forall (blist blist': list bexp_stack) vals k a aval fenv stk stk',
  transformed_prop_exprs_args (V := bool) (bool_update_rel k a) blist blist' ->
  aexp_stack_pure_rel a fenv ->
  aexp_stack_sem a fenv stk (stk, aval) ->
  stack_mutated_at_index stk' k aval stk ->
  prop_args_rel (V := bool) (fun (boolexpr: bexp_stack) => bexp_stack_pure_rel boolexpr fenv) blist ->
  eval_prop_args_rel (fun (boolexpr: bexp_stack) (boolval: bool) => bexp_stack_sem boolexpr fenv stk (stk, boolval)) blist' vals ->
  eval_prop_args_rel (fun (boolexpr: bexp_stack) (boolval: bool) => bexp_stack_sem boolexpr fenv stk' (stk', boolval)) blist vals.
Proof.
  induction blist; intros blist' vals k aexpr aval fenv stk stk' UPDATE PURE_A AEXP MUTATE LIST_PURE EVAL.
  - invs UPDATE.
    invs EVAL. econstructor.
  - invs UPDATE. invs EVAL.
    econstructor.
    + eapply bool_substitution_vs_update; try eassumption.
      eapply bool_update_implies_pure; try eassumption.
      invs LIST_PURE.
      * eapply bexp_purity_implies_well_formed; eassumption.
      * invs LIST_PURE.
        eapply bool_update_preserves_bexp_pure; eassumption.
    + eapply IHblist; try eassumption.
      invs LIST_PURE.
      eassumption.
Qed.

  
Lemma eval_prop_rel_help :
  forall (l l': LogicProp bool bexp_stack) k a aval fenv stk stk',
    transformed_prop_exprs (bool_update_rel k a) l l' ->
    aexp_stack_pure_rel a fenv ->
    aexp_stack_sem a fenv stk (stk, aval) ->
    stack_mutated_at_index stk' k aval stk ->
    prop_rel (fun (boolexpr: bexp_stack) => bexp_stack_pure_rel boolexpr fenv) l ->
    eval_prop_rel (fun (boolexpr: bexp_stack) (boolval: bool) => bexp_stack_sem boolexpr fenv stk (stk, boolval)) l' ->
    eval_prop_rel (fun (boolexpr: bexp_stack) (boolval: bool) => bexp_stack_sem boolexpr fenv stk' (stk', boolval)) l.
Proof.
  intros l l' k a aval fenv stk stk' H. revert aval fenv stk stk'.
  remember (bool_update_rel k a).
  dependent induction H; intros.
  - constructor.
  - invs H3.
  - invs H3. invs H4. econstructor; eauto.
    eapply bool_substitution_vs_update; eauto.
  - invs H4. invs H5. 
    econstructor; eauto; eapply bool_substitution_vs_update; eauto.
  - invs H4. invs H5. econstructor; eauto.
  - invs H4. invs H5.
    + eapply RelOrPropLeft; eauto.
    + eapply RelOrPropRight; eauto.
  - invs H5. invs H6. 
    econstructor; eauto; eapply bool_substitution_vs_update; eauto.
  - invs H3. invs H4.
    econstructor; eauto.
    eapply eval_prop_args_rel_help; eassumption.
Qed.


Lemma arith_eval_prop_args_rel_help :
  forall (a_list : list aexp_stack) (k : stack_index) (a : aexp_stack) (aval : nat) (fenv : fun_env_stk) (stk stk' : stack) (a_list' : list aexp_stack) (vals: list nat),
    aexp_stack_pure_rel a fenv ->
    aexp_stack_sem a fenv stk (stk, aval) ->
    stack_mutated_at_index stk' k aval stk ->
    transformed_prop_exprs_args (V:= nat) (arith_update_rel k a) a_list a_list' ->
    eval_prop_args_rel (fun (boolexpr : aexp_stack) (boolval : nat) => aexp_stack_sem boolexpr fenv stk (stk, boolval)) a_list' vals ->
    prop_args_rel (V := nat) (fun boolexpr : aexp_stack => aexp_stack_pure_rel boolexpr fenv) a_list ->
    eval_prop_args_rel (fun (boolexpr : aexp_stack) (boolval : nat) => aexp_stack_sem boolexpr fenv stk' (stk', boolval)) a_list vals.
Proof.
  induction a_list as [ | arg args ]; intros k a aval fenv stk stk' a_list' vals PURE_A SEM MUTATE UPDATE EVAL PURE; invc UPDATE; invc PURE; invc EVAL.
  - econstructor.
  - econstructor.
    + eapply arith_substitution_vs_update; eassumption.
    + eapply IHargs; [ eapply PURE_A | .. ]; eassumption.
Qed.      

Lemma arith_eval_prop_rel_help :
  forall (l l': LogicProp nat aexp_stack) k a aval fenv stk stk',
    transformed_prop_exprs (arith_update_rel k a) l l' ->
    aexp_stack_pure_rel a fenv ->
    aexp_stack_sem a fenv stk (stk, aval) ->
    stack_mutated_at_index stk' k aval stk ->
    prop_rel (fun (boolexpr: aexp_stack) => aexp_stack_pure_rel boolexpr fenv) l ->
    eval_prop_rel (fun (boolexpr: aexp_stack) (boolval: nat) => aexp_stack_sem boolexpr fenv stk (stk, boolval)) l' ->
    eval_prop_rel (fun (boolexpr: aexp_stack) (boolval: nat) => aexp_stack_sem boolexpr fenv stk' (stk', boolval)) l.
Proof.
  induction l as [ | | ?f ?arg | | | | | ]; intros l' k a aval fenv stk stk' TRANSFORM PURE_A AVAL MUTATE PURE EVAL; invc TRANSFORM; invc EVAL; invc PURE; try solve [ econstructor | econstructor; try eassumption; eapply arith_substitution_vs_update; try eassumption ].
  - econstructor.
    + eapply IHl1; try eassumption.
    + eapply IHl2; eassumption.
  - econstructor. eapply IHl1; eassumption.
  - eapply RelOrPropRight. eapply IHl2; eassumption.
  - econstructor; [ | eassumption ].
    eapply arith_eval_prop_args_rel_help; eassumption.
Qed.


Lemma prop_rel_pure_help :
  forall a_list a fenv k a_list0,
    aexp_stack_pure_rel a fenv ->
    prop_args_rel (V := bool) bexp_well_formed a_list0 ->
    transformed_prop_exprs_args (V := bool) (bool_update_rel k a) a_list0 a_list ->
    prop_args_rel (V := bool) (fun (boolexpr : bexp_stack) => bexp_stack_pure_rel boolexpr fenv) a_list ->
    prop_args_rel (V := bool) (fun (boolexpr : bexp_stack) => bexp_stack_pure_rel boolexpr fenv) a_list0.
Proof.
  induction a_list as [ | arg args]; intros a  fenv k a_list0 PURE_A WF UPDATE PURE; invs UPDATE; invs PURE; invs WF; econstructor.
  + eapply bool_update_pure_implies_bexp_pure; eassumption.
  + eapply IHargs; eassumption.
Qed.

Lemma arith_prop_rel_pure_help :
  forall a_list a fenv k a_list0,
    aexp_stack_pure_rel a fenv ->
    prop_args_rel (V := nat) aexp_well_formed a_list0 ->
    transformed_prop_exprs_args (V := nat) (arith_update_rel k a) a_list0 a_list ->
    prop_args_rel (V := nat) (fun (boolexpr : aexp_stack) => aexp_stack_pure_rel boolexpr fenv) a_list ->
    prop_args_rel (V := nat) (fun (boolexpr : aexp_stack) => aexp_stack_pure_rel boolexpr fenv) a_list0.
Proof.
  induction a_list as [ | arg args]; intros a fenv k a_list0 PURE_A WF UPDATE PURE; invs UPDATE; invs PURE; invs WF; econstructor.
  + eapply arith_update_pure_implies_purity; eauto.
  + apply (IHargs a fenv k args0 PURE_A H7 H4); auto.
Qed.

Lemma transformed_prop_pure_help :
  forall l a fenv k l0,
    aexp_stack_pure_rel a fenv ->
    prop_rel (V := bool) bexp_well_formed l0 ->
    prop_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) l ->
    transformed_prop_exprs (bool_update_rel k a) l0 l ->
    prop_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) l ->
    prop_rel (V := bool) (fun boolexpr : bexp_stack => bexp_stack_pure_rel boolexpr fenv) l0.
Proof.
  induction l; intros b fenv k l0 PURE_A WF UPDATE PURE; invs UPDATE; auto; invs PURE; invs WF;
  econstructor; try eapply bool_update_implies_pure; eauto.
  eapply prop_rel_pure_help; eauto.
Qed.

Lemma transformed_prop_aexp_pure_help :
  forall a k l0 l fenv,
    transformed_prop_exprs (arith_update_rel k a) l0 l ->
    prop_rel (V := nat) aexp_well_formed l0 ->
    aexp_stack_pure_rel a fenv ->
    prop_rel (V := nat) (fun aexpexpr : aexp_stack => aexp_stack_pure_rel aexpexpr fenv) l ->
    prop_rel (V := nat) (fun aexpexpr : aexp_stack => aexp_stack_pure_rel aexpexpr fenv) l0.
Proof.
  intros a k l0 l fenv H. remember (arith_update_rel k a).
  Ltac invc_prop_rel :=
    match goal with
    | [ H : prop_rel (fun _ => aexp_stack_pure_rel _
                     _) (_ _) |- _ ] =>
        progress invc H; try (invc_prop_rel)
    | [ H : prop_rel aexp_well_formed (_ _) |- _ ] =>
        progress invc H; try (invc_prop_rel)
    end.
  induction H; intros; auto; invc_prop_rel; econstructor; try eapply arith_update_implies_pure; eauto.
  eapply arith_prop_rel_pure_help; eauto. 
Qed.

Lemma meta_match_rel_same_as_eval_under_different_state :
  forall M M' k a aval fenv stk stk',
    mv_well_formed M ->
    meta_update_rel k a M M' ->
    aexp_stack_pure_rel a fenv ->
    aexp_stack_sem a fenv stk (stk, aval) ->
    stack_mutated_at_index stk' k aval stk ->
    meta_match_rel M' fenv stk ->
    meta_match_rel M fenv stk'.
Proof.
  intros M M' k a aval fenv stk stk' WF UPDATE PURE AEXP MUTATE MATCH.
  invs MATCH.
  - invs UPDATE. constructor.
    + revert H5 H0 H MUTATE AEXP UPDATE WF. revert l0.
      revert stk' PURE MATCH. revert k a aval fenv stk.
      induction l; intros; invs UPDATE; invs H6; invs H; invs H0; invs WF; invs H2.
      * econstructor.
      * econstructor; bool_sub_update.
      * econstructor; bool_sub_update.
      * econstructor; eauto. 
        -- eapply IHl1; eauto; econstructor; eauto.
        -- eapply IHl2; eauto; econstructor; eauto.
      * econstructor.
        eapply IHl1; eauto; econstructor; eauto.
      * eapply RelOrPropRight.
        eapply IHl2; eauto; econstructor; eauto.
      * econstructor; bool_sub_update.
      * eapply eval_prop_rel_help; eauto.
        invs H4; econstructor; [ econstructor | .. ].
        invs H3. invs H2.
        invs H13.
        econstructor.
        eapply bool_update_pure_implies_bexp_pure; try eassumption.
        eapply prop_rel_pure_help; eauto.
    + invs WF. eapply transformed_prop_pure_help; eassumption.
  - invs UPDATE. invs WF. constructor; [ | eapply transformed_prop_aexp_pure_help; eassumption ].
    revert H5 H0 H MUTATE AEXP UPDATE H2 WF. revert l0.
    induction l; intros; invs UPDATE; invs H5; invs H; invs H0; invs H2.
    + econstructor.
    + econstructor; arith_sub_update.
    + econstructor; arith_sub_update.
    + econstructor.
      * eapply IHl1; eauto; econstructor; eauto.
      * eapply IHl2; eauto; econstructor; eauto.
    + econstructor. eapply IHl1; eauto; econstructor; eauto.
    + eapply RelOrPropRight. eapply IHl2; eauto; econstructor; eauto.
    + econstructor; arith_sub_update.
    + eapply arith_eval_prop_rel_help; try eassumption.
      econstructor.
      eapply arith_prop_rel_pure_help; eassumption.
Qed.

Lemma state_update_same_as_eval_under_different_state :
  forall P P' k (a: aexp_stack) (aval: nat) fenv stk stk',
    state_update_rel k a P P' -> (* P[k := a] = P' *)
    aexp_stack_pure_rel a fenv ->
    absstate_well_formed P ->
    aexp_stack_sem a fenv stk (stk, aval) -> (* a evaluates to aval *)
    stack_mutated_at_index stk' k aval stk -> (* stk' = stk''[k := aval] *)
    absstate_match_rel P' fenv stk -> (* stk is contained in P' *)
    absstate_match_rel P fenv stk'. (* stk' is contained in P *)
Proof.
  induction P; intros ? ? ? ? ? ? ? ? PURE WF; intros.
  - invs H. invs H2.
    econstructor.
    + invs H7.
      * econstructor.
      * pose proof (stack_mutation_preserves_length).
        inversion H1.
        -- assert (1 <= k) by intuition.
           assert (k <= Datatypes.length (aval :: stk0)).
           simpl.
           match goal with
           | [ H : 1 = k |- _ ] =>
               rewrite <- H
           | [ H : k = 1 |- _ ] =>
               rewrite H
           end.
           intuition.
           econstructor.
           simpl.
           eapply (H4 stk stk' k aval) in H16.
           assert (Datatypes.length (new :: stk0) = Datatypes.length stk') by (f_equal; assumption).
           simpl in H18.
           rewrite H18.
           rewrite <- H16. assumption.
           subst.
           simpl in H17.
           simpl.
           assumption.
           assumption.
        -- assert (1 <= k) by intuition.
           pose proof (Hleq := H20).
           eapply H4 with (stk := stk) (stk' := stk') in H20.
           assert (Datatypes.length (n :: stk0) = Datatypes.length stk') by (f_equal; assumption).
           assert (Datatypes.length (n' :: stk'0) = Datatypes.length stk) by (f_equal; assumption).
           econstructor.
           rewrite H21.
           rewrite <- H20. assumption.
           invs H11.
           intuition.
           
           eassumption.
    + invs H5; invs WF; eapply meta_match_rel_same_as_eval_under_different_state; try eassumption.
  - invs WF. invs H.  invs H2. econstructor.
    + eapply IHP1; eassumption.
    + eapply IHP2; eassumption.
  - invs WF. invs H. invs H2.
    + econstructor. eapply IHP1; eassumption.
    + eapply RelAbsOrRight. eapply IHP2; eassumption.
Qed.



Definition aexp_args_P' (a a': aexp_stack) (n: nat): Prop :=
  forall (fenv: fun_env_stk) (stk stk': stack) (v: nat),
    List.length stk' = n ->
    aexp_stack_pure_rel a fenv ->
    aexp_stack_sem a fenv stk (stk, v) ->
    aexp_stack_sem a' fenv (stk' ++ stk) (stk' ++ stk, v).

Definition aexp_args_P0' (l l': list aexp_stack) (n: nat): Prop :=
  forall (fenv: fun_env_stk) (stk stk': stack) (vs: list nat),
    List.length stk' = n ->
    args_stack_pure_rel l fenv ->
    args_stack_sem l fenv stk (stk, vs) ->
    args_stack_sem l' fenv (stk' ++ stk) (stk' ++ stk, vs).


Lemma aexp_args_stack_increase_preserves_eval' :
  (forall (n: nat) (a a': aexp_stack),
      aexp_stk_size_inc_rel n a a' ->
      aexp_args_P' a a' n) /\
    (forall (n: nat) (l l': list aexp_stack),
        args_stk_size_inc_rel n l l' ->
        aexp_args_P0' l l' n).
Proof.
  pose (fun (n: nat) (a a0: aexp_stack) =>
        fun (H: aexp_stk_size_inc_rel n a a0) =>
          aexp_args_P' a a0 n) as P.
  pose (fun (n: nat) (l l0 : list aexp_stack) =>
        fun (H: args_stk_size_inc_rel n l l0) =>
          aexp_args_P0' l l0 n) as P0.
  
  apply (aexp_args_size_inc_rel_mut_ind P P0); intros; unfold P, P0 in *; unfold aexp_args_P', aexp_args_P0' in *; intros fenv stk stk' v STKLEN PURE SEM.
  - invs SEM. econstructor.
  - invs SEM. econstructor.
    + intuition.
    + rewrite app_length. intuition.
    + enough (Datatypes.length stk' <= k + Datatypes.length stk' - 1).
      * rewrite nth_error_app2; [ | assumption].
        enough (k + Datatypes.length stk' - 1 - Datatypes.length stk' = k - 1).
        -- rewrite H0. assumption.
        -- intuition.
      * intuition.
  - invs SEM.
    invs PURE.
    assert (stk1 = stk) by (eapply aexp_stack_pure_backwards with (a := a2); eassumption).
    subst. econstructor; [ eapply H | eapply H0]; eauto.
  - invs SEM. invs PURE.
    assert (stk1 = stk) by (eapply aexp_stack_pure_backwards with (a := a2); eassumption).
    subst.
    econstructor; [ eapply H | eapply H0 ]; eauto.
  - inversion SEM. revert H4 H6 H7. subst. invs PURE. intros.
    pose proof (H10 := H9).
    pose proof (H11 := H3).
    eapply args_stack_pure_implication in H10.
    rewrite H10 in *. clear H10.
    2: assumption.
    pose proof (IMP_FRAME_COPY := H4).
    eapply frame_stk in IMP_FRAME_COPY.
    2: rewrite H0; eassumption.
    
    pose proof (frame_implies_rest_stk_untouched_le).
    specialize (H2 (Body func)   (Args (fenv f)) (Return_pop (fenv f)) (fenv) stk2 vals stk1).
    pose proof (IMP := H12).
    pose proof (IMP_FRAME := H4).
    rewrite <- H0 in H2.
    rewrite Nat.add_comm in H4.
    apply H2 in H4.
    destruct H4.
    destruct H4.
    rewrite H10 in *.
    econstructor.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eapply args_stk_size_inc_preserves_args_length.
      eassumption.
    + eapply H.
      * reflexivity.
      * assumption.
      * eassumption.
    + enough (imp_stack_sem (Body func) fenv (vals ++ stk' ++ stk1) (x ++ stk' ++ stk1)).
      eassumption.
      eapply frame_implies_intervening_stk_okay; [ | subst .. ].
      rewrite <- H0. rewrite Nat.add_comm in IMP_FRAME.
      eassumption.
      rewrite H8.
      eapply args_stack_sem_preserves_length.
      eassumption.
      symmetry.

      assumption.
      assumption.
    + 
      eapply aexp_frame_pure.
      rewrite <- H0 in H6.
      rewrite <- H6 in H13.
      pose proof (AEXP_RET := H13).
      eapply pure_aexp_implies_same_stack in H13; [ | eassumption ].
      rewrite <- H13 in AEXP_RET.
      rewrite H6 in AEXP_RET.
      eassumption.
      rewrite H4.
      rewrite Nat.add_comm.
      rewrite <- H6. rewrite <- H0.
      assumption.
    + rewrite <- H8. rewrite <- H1. rewrite <- H0.
      eapply same_after_popping_length.
      eassumption.
    + eapply args_stack_sem_preserves_length in H9.
      rewrite <- H9. rewrite <- H0 in H8.
      assumption.
    + subst. eapply same_after_popping_implies_geq_popped_length.
      rewrite Nat.add_comm.
      aexp_pure (Return_expr (fenv f)). eauto.
    + rewrite H0. assumption.
  - invs SEM. econstructor.
  - invs SEM. invs PURE.
    aexp_pure arg.
    econstructor; [ eapply H | eapply H0]; eauto.
Qed.

Definition aexp_args_P (a a': aexp_stack) (n: nat): Prop :=
  forall (fenv: fun_env_stk) (stk stk': stack) (v: nat),
    List.length stk' = n ->
    aexp_well_formed a ->
    aexp_stack_pure_rel a' fenv ->
    aexp_stack_sem a' fenv (stk' ++ stk) (stk' ++ stk, v) ->
    aexp_stack_sem a fenv stk (stk, v).

Definition aexp_args_P0 (l l': list aexp_stack) (n: nat): Prop :=
  forall (fenv: fun_env_stk) (stk stk': stack) (vs: list nat),
    List.length stk' = n ->
    args_well_formed l ->
    args_stack_pure_rel l' fenv ->
    args_stack_sem l' fenv (stk' ++ stk) (stk' ++ stk, vs) ->
    args_stack_sem l fenv stk (stk, vs).

Lemma m_plus_n_minus_one_minus_n_is_m_minus_one :
  forall (m n: nat),
    m + n - 1 - n = m - 1.
Proof.
  intros. lia.
Qed.

Lemma aexp_args_stack_increase_preserves_eval'' :
  (forall (n: nat) (a a': aexp_stack),
      aexp_stk_size_inc_rel n a a' ->
      aexp_args_P a a' n) /\
    (forall (n: nat) (l l': list aexp_stack),
        args_stk_size_inc_rel n l l' ->
        aexp_args_P0 l l' n).
Proof.
  pose (fun (n: nat) (a a0: aexp_stack) =>
        fun (H: aexp_stk_size_inc_rel n a a0) =>
          aexp_args_P a a0 n) as P.
  pose (fun (n: nat) (l l0 : list aexp_stack) =>
        fun (H: args_stk_size_inc_rel n l l0) =>
          aexp_args_P0 l l0 n) as P0.
  apply (aexp_args_size_inc_rel_mut_ind P P0); intros; unfold P, P0 in *; unfold aexp_args_P, aexp_args_P0 in *; intros fenv stk stk' v STKLEN WF PURE SEM; inversion SEM.
  - econstructor.
  - econstructor. rewrite List.app_length in H2.
    destruct k, stk'.
    + simpl in H1. invs H1; simpl in H1; invs H1.
    + invs PURE.
      invs WF.
      invs H0.
      
    + intuition.
    + intuition.
    + rewrite List.app_length in H2. intuition.
    + rewrite nth_error_app2 in H5.
      * subst. rewrite m_plus_n_minus_one_minus_n_is_m_minus_one in H5. assumption.
      * rewrite <- STKLEN. destruct (Datatypes.length stk') eqn:len.
        -- subst. rewrite Nat.add_0_r. rewrite Nat.add_0_r in H1. intuition.
        -- rewrite Nat.add_comm. invs WF. intuition.
  - inversion WF. invs PURE. econstructor.
    + eapply H.
      * reflexivity.
      * eassumption.
      * assumption.
      * assert (stk1 = stk' ++ stk) by (eapply aexp_stack_pure_backwards with (a := a2'); eassumption). subst.
        eassumption.
    + eapply H0; eauto.
      assert (stk1 = stk' ++ stk) by (eapply aexp_stack_pure_backwards with (a := a2'); eassumption). subst. eassumption.
  - inversion WF. econstructor.
    + eapply H; [ | invs PURE .. ]; try eassumption.
      aexp_pure a1'. assumption.
    + eapply H0; [ | invs PURE .. ]; try eassumption.
      aexp_pure a2'. assumption.
  - revert H4 H5 H6 H7 H8. invs PURE.
    rewrite Nat.add_comm in H8.
    assert (Datatypes.length args' = Datatypes.length vals) by (eapply args_stack_sem_preserves_length; eassumption).
    pose proof (FRAME := H8).
    intros. rewrite <- H4 in * |- .
    rewrite H2 in H5.
    eapply frame_implies_rest_stk_untouched_le in H8; [ | rewrite H0 in H5; eassumption | | eassumption ].
    destruct H8.
    destruct H3. rewrite H8 in * |- .
    rewrite <- H3 in FRAME.
    assert (Datatypes.length args' = Datatypes.length vals) by (eapply args_stack_sem_preserves_length; eassumption).
    rewrite H10 in H5.
    rewrite H5 in FRAME.
    eapply frame_preserves_rest_stk with (stk := stk1) (stk' := stk) in FRAME; [ | assumption ].
    rewrite H4 in * |- .
    rewrite <- H10 in H5.
    rewrite <- H2 in H5.
    econstructor; try eassumption.
    + eapply args_stk_size_inc_preserves_args_length in a. rewrite <- a in H2. assumption.
    + eapply H.
      * assert (Datatypes.length stk' = Datatypes.length stk') by reflexivity. eassumption.
      * invs WF. assumption.
      * invs PURE. assumption.
      * invs PURE. invs WF. eapply args_size_inc_preserves_purity' in a; [ | eassumption .. ].
        args_pure args'.
        rewrite <- SAME in H9. eassumption.
    + rewrite H6 in H17. aexp_pure ret_expr.
      eapply aexp_frame_pure.
      eassumption.
      rewrite Nat.add_comm in H15. rewrite <- H3 in H15. assumption.
    + rewrite H5 in H3. rewrite H1 in H3. eapply same_after_popping_length. assumption.
    + clear P. clear P0. subst. aexp_pure (Return_expr (fenv f)).
      rewrite Nat.add_comm in H14. rewrite <- H5 in H14.
      eapply same_after_popping_implies_geq_popped_length; eauto.
  - subst. constructor.
  - subst. econstructor.
    + eapply H.
      * assert (Datatypes.length stk' = Datatypes.length stk') by reflexivity.
        eassumption.
      * invs WF. assumption.
      * invs PURE. assumption.
      * invs PURE.
        aexp_pure arg'.
        assumption.
    + eapply H0.
      * assert (Datatypes.length stk' = Datatypes.length stk') by reflexivity.
        eassumption.
      * invs WF. assumption.
      * invs PURE. assumption.
      * invs SEM.
        invs PURE.
        aexp_pure arg'. assumption.
Qed.



Lemma cons_is_append_singleton_list :
  forall (A: Type) (a: A) (l: list A),
    a :: l = (a :: nil) ++ l.
Proof.
  intros. induction l; auto.
Qed.

(** For every one of the following lemmas, there's a version with a ' after it
 *  and a version without a ' after it. This is proving both directions of what
 *  could have been a single theorem. Essentially, our semantics only cares
 *  about the part of the stack that is actually used in an expression. 
 *
 *  The versions with no ' are used for push, and the versions with ' are used
 *  for pop. *)
Lemma aexp_stack_increase_preserves_eval :
  forall a a' fenv stk v,
    aexp_stk_size_inc_rel 1 a a' ->
    aexp_stack_pure_rel a fenv ->
    aexp_stack_sem a fenv stk (stk, v) ->
    aexp_stack_sem a' fenv (0 :: stk) (0 :: stk, v).
Proof.
  pose proof (aexp_args_stack_increase_preserves_eval') as AEXP_ARGS.
  unfold aexp_args_P' in AEXP_ARGS.
  destruct AEXP_ARGS as (AEXP & _).
  intros. specialize (AEXP 1).
  enough (0 :: stk = (0 :: nil) ++ stk).
  - rewrite H2.
    eapply AEXP; try eassumption.
    reflexivity.
  - simpl. reflexivity.
Qed.

(** Also, all of the versions with ' have an extra clause about the well-formed-ness
 *  of variables inside of the expression -- i.e., all of the stack variables of
 *  the form #k have k >= 1. That way, we essentially know that a' doesn't 
 *  reference #1, since all the variables in a' have been increased by 1. *)
Lemma aexp_stack_increase_preserves_eval' :
  forall a a' fenv stk v f,
    aexp_stk_size_inc_rel 1 a a' ->
    aexp_well_formed a ->
    aexp_stack_pure_rel a fenv ->
    aexp_stack_sem a' fenv (f :: stk) (f :: stk, v) ->
    aexp_stack_sem a fenv stk (stk, v).
Proof.
  pose proof (aexp_args_stack_increase_preserves_eval'') as AEXP_ARGS.
  unfold aexp_args_P in AEXP_ARGS.
  destruct AEXP_ARGS as (AEXP & _).
  intros. specialize (AEXP 1).
  rewrite cons_is_append_singleton_list in H2.
  eapply AEXP; try eassumption.
  reflexivity.
  eapply aexp_size_inc_preserves_purity; eassumption.
Qed.


Lemma args_stack_increase_preserves_eval :
  forall args args' fenv stk vals,
    args_stk_size_inc_rel 1 args args' ->
    args_stack_pure_rel args fenv ->
    args_stack_sem args fenv stk (stk, vals) ->
    args_stack_sem args' fenv (0 :: stk) (0 :: stk, vals).
Proof.
  pose proof (aexp_args_stack_increase_preserves_eval') as AEXP_ARGS.
  unfold aexp_args_P0' in AEXP_ARGS.
  destruct AEXP_ARGS as (_ & ARGS).
  intros. specialize (ARGS 1).
  rewrite cons_is_append_singleton_list.
  eapply ARGS; try eassumption.
  reflexivity.
Qed.

Lemma args_stack_increase_preserves_eval' :
  forall args args' fenv stk vals v,
    args_stk_size_inc_rel 1 args args' ->
    args_well_formed args ->
    args_stack_pure_rel args fenv ->
    args_stack_sem args' fenv (v :: stk) (v :: stk, vals) ->
    args_stack_sem args fenv stk (stk, vals).
Proof.
  pose proof (aexp_args_stack_increase_preserves_eval'') as AEXP_ARGS.
  unfold aexp_args_P0 in AEXP_ARGS.
  destruct AEXP_ARGS as (_ & ARGS).
  intros. specialize (ARGS 1).
  rewrite cons_is_append_singleton_list in H2.
  eapply ARGS; try eassumption.
  reflexivity.
  eapply args_size_inc_preserves_purity; eassumption.
Qed.

Lemma bexp_stack_increase_preserves_eval_stronger :
  forall b b' fenv stk stk' stk'' v n,
    bexp_stk_size_inc_rel n b b' ->
    n = Datatypes.length stk' ->
    bexp_stack_pure_rel b fenv ->
    bexp_stack_sem b fenv stk (stk'', v) ->
    bexp_stack_sem b' fenv (stk' ++ stk) (stk' ++ stk'', v).
Proof.
  intros b b' fenv stk stk' stk'' v n H. revert v stk'' stk' stk fenv.
  dependent induction H; intros.
  - invs H1. constructor.
  - invs H1. constructor.
  - invs H2. invs H1. eapply Stack_neg; eauto.
  - invs H2. invs H3. eapply Stack_and; eauto.
  - invs H2. invs H3. eapply Stack_or; eauto.
  - invs H2. invs H3. aexp_pure a1. aexp_pure a2. 
    pose proof aexp_args_stack_increase_preserves_eval'.
    unfold aexp_args_P' in H1. unfold aexp_args_P0 in H1.
    destruct H1. econstructor; eauto.
  - invs H2. invs H3. aexp_pure a1. aexp_pure a2.
    pose proof aexp_args_stack_increase_preserves_eval'.
    unfold aexp_args_P' in H1. unfold aexp_args_P0 in H1.
    destruct H1. econstructor; eauto.
Qed.

Lemma bexp_stack_increase_preserves_eval_strong :
  forall b b' fenv stk stk' v n,
    bexp_stk_size_inc_rel n b b' ->
    n = Datatypes.length stk' ->
    bexp_stack_pure_rel b fenv ->
    bexp_stack_sem b fenv stk (stk, v) ->
    bexp_stack_sem b' fenv (stk' ++ stk) (stk' ++ stk, v).
Proof.
  intros. eapply bexp_stack_increase_preserves_eval_stronger; eauto.
Qed.

Lemma bexp_stack_increase_preserves_eval :
  forall b b' fenv stk v,
    bexp_stk_size_inc_rel 1 b b' ->
    bexp_stack_pure_rel b fenv ->
    bexp_stack_sem b fenv stk (stk, v) ->
    bexp_stack_sem b' fenv (0 :: stk) (0 :: stk, v).
Proof.
  intros. rewrite cons_is_append_singleton_list.
  eapply bexp_stack_increase_preserves_eval_strong; eauto.
Qed.

Lemma app_inv:
  forall {A} (l1 l2 l3 : list A),
    l1 ++ l2 = l1 ++ l3 ->
    l2 = l3.
Proof.
  induction l1; intros; auto.
  inversion H. inversion H1. auto.
Qed.

Lemma bexp_stack_increase_preserves_eval_stronger' :
  forall b b' fenv stk stk' stk'' v n,
    bexp_stk_size_inc_rel n b b' ->
    n = Datatypes.length stk' ->
    bexp_well_formed b ->
    bexp_stack_pure_rel b fenv ->
    bexp_stack_sem b' fenv (stk' ++ stk) (stk' ++ stk'', v) ->
    bexp_stack_sem b fenv stk (stk'', v).
Proof.
  intros b b' fenv stk stk' stk'' v n H. revert v stk stk' stk'' fenv.
  dependent induction H; intros.
  - invs H2. apply app_inv in H3. subst. constructor.
  - invs H2. apply app_inv in H3. subst. constructor.
  - invs H3. eapply Stack_neg; eauto.
    eapply IHbexp_stk_size_inc_rel; eauto.
    + invs H1. auto.
    + invs H2. auto.
  - invs H4. invs H3. invs H2. 
    pose proof (bexp_size_inc_preserves_purity b1 b1' (Datatypes.length stk') fenv H H6).
    pose proof (bexp_size_inc_preserves_purity b2 b2' (Datatypes.length stk') fenv H0 H8).      
    bexp_pure b1'. bexp_pure b2'. eapply Stack_and; eauto.
  - invs H4. invs H3. invs H2. 
    pose proof (bexp_size_inc_preserves_purity b1 b1' (Datatypes.length stk') fenv H H6).
    pose proof (bexp_size_inc_preserves_purity b2 b2' (Datatypes.length stk') fenv H0 H8).      
    bexp_pure b1'. bexp_pure b2'. eapply Stack_or; eauto.
  - invs H4. invs H3. invs H2.
    pose proof (aexp_size_inc_preserves_purity a1 a1' (Datatypes.length stk') fenv H H6).
    pose proof (aexp_size_inc_preserves_purity a2 a2' (Datatypes.length stk') fenv H0 H8).      
    aexp_pure a1'. aexp_pure a2'. 
    pose proof aexp_args_stack_increase_preserves_eval''.
    unfold aexp_args_P in H10. unfold aexp_args_P0 in H10. destruct H10.
    eapply app_inv in SAME; subst. econstructor; eauto.
  - invs H4. invs H3. invs H2.
    pose proof (aexp_size_inc_preserves_purity a1 a1' (Datatypes.length stk') fenv H H6).
    pose proof (aexp_size_inc_preserves_purity a2 a2' (Datatypes.length stk') fenv H0 H8).      
    aexp_pure a1'. aexp_pure a2'. 
    pose proof aexp_args_stack_increase_preserves_eval''.
    unfold aexp_args_P in H10. unfold aexp_args_P0 in H10. destruct H10.
    eapply app_inv in SAME; subst. econstructor; eauto.
Qed.

Lemma bexp_stack_increase_preserves_eval_strong' :
  forall b b' fenv stk stk' v n,
    bexp_stk_size_inc_rel n b b' ->
    n = Datatypes.length stk' ->
    bexp_well_formed b ->
    bexp_stack_pure_rel b fenv ->
    bexp_stack_sem b' fenv (stk' ++ stk) (stk' ++ stk, v) ->
    bexp_stack_sem b fenv stk (stk, v).
Proof.
  intros. eapply bexp_stack_increase_preserves_eval_stronger'; eauto.
Qed.

Lemma bexp_stack_increase_preserves_eval' :
  forall b b' fenv stk v f,
    bexp_stk_size_inc_rel 1 b b' ->
    bexp_well_formed b ->
    bexp_stack_pure_rel b fenv ->
    bexp_stack_sem b' fenv (f :: stk) (f :: stk, v) ->
    bexp_stack_sem b fenv stk (stk, v).
Proof.
  intros. rewrite cons_is_append_singleton_list in H2.
  eapply bexp_stack_increase_preserves_eval_strong'; eauto. auto.
Qed.

Lemma bool_args_stack_increase_preserves_eval :
  forall a_list args' fenv stk vals0,
    transformed_prop_exprs_args (V := bool) (bexp_stk_size_inc_rel 1) a_list args' ->
    prop_args_rel (V := bool) (fun (boolexpr: bexp_stack) => bexp_stack_pure_rel boolexpr fenv) a_list ->
    eval_prop_args_rel (fun (boolexpr : bexp_stack) (boolval : bool) => bexp_stack_sem boolexpr fenv stk (stk, boolval)) a_list vals0 ->
    eval_prop_args_rel (fun (boolexpr : bexp_stack) (boolval : bool) => bexp_stack_sem boolexpr fenv (0 :: stk) (0 :: stk, boolval)) args' vals0.
Proof.
  intros a_list args' fenv stk vals0 H. remember (bexp_stk_size_inc_rel 1).
  revert vals0 stk fenv.
  induction H; intros.
  - invs H0. constructor.
  - invs H2. invs H1. eapply RelArgsCons; eauto. 
    eapply bexp_stack_increase_preserves_eval; eauto.
Qed.

Lemma bool_args_stack_increase_preserves_eval' :
  forall a_list args' fenv stk vals0 v, 
    transformed_prop_exprs_args (V := bool) (bexp_stk_size_inc_rel 1) a_list args' ->
    bool_prop_args_wf a_list ->
    prop_args_rel (V := bool) (fun (boolexpr: bexp_stack) => bexp_stack_pure_rel boolexpr fenv) a_list ->
    eval_prop_args_rel (fun (boolexpr : bexp_stack) (boolval : bool) => bexp_stack_sem boolexpr fenv (v :: stk) (v :: stk, boolval)) args' vals0 ->
    eval_prop_args_rel (fun (boolexpr : bexp_stack) (boolval : bool) => bexp_stack_sem boolexpr fenv stk (stk, boolval)) a_list vals0.
Proof.
  intros a_list args' fenv stk vals0 v H. remember (bexp_stk_size_inc_rel 1).
  revert vals0 stk fenv v.
  induction H; intros.
  - invs H0. invs H1. constructor.
  - invs H2. invs H3. invs H1. eapply RelArgsCons; eauto.
    eapply bexp_stack_increase_preserves_eval'; eauto.
Qed.

Lemma nat_args_stack_increase_preserves_eval :
  forall a_list args' fenv stk vals0,
    transformed_prop_exprs_args (V := nat) (aexp_stk_size_inc_rel 1) a_list args' ->
    prop_args_rel (V := nat) (fun (natexpr: aexp_stack) => aexp_stack_pure_rel natexpr fenv) a_list ->
    eval_prop_args_rel (fun (expr : aexp_stack) (val : nat) => aexp_stack_sem expr fenv stk (stk, val)) a_list vals0 ->
    eval_prop_args_rel (fun (expr : aexp_stack) (val : nat) => aexp_stack_sem expr fenv (0 :: stk) (0 :: stk, val)) args' vals0.
Proof.
  intros a_list args' fenv stk vals0 H. remember (aexp_stk_size_inc_rel 1).
  revert vals0 stk fenv.
  induction H; intros.
  - invs H0. constructor.
  - invs H2. invs H1. eapply RelArgsCons; eauto. 
    eapply aexp_stack_increase_preserves_eval; eauto.
Qed.

Lemma nat_args_stack_increase_preserves_eval' :
  forall a_list args' fenv stk vals0 v,
    transformed_prop_exprs_args (V := nat) (aexp_stk_size_inc_rel 1) a_list args' ->
    nat_prop_args_wf a_list ->
    prop_args_rel (V := nat) (fun (natexpr: aexp_stack) => aexp_stack_pure_rel natexpr fenv) a_list ->
    eval_prop_args_rel (fun (expr : aexp_stack) (val : nat) => aexp_stack_sem expr fenv (v :: stk) (v :: stk, val)) args' vals0 ->
    eval_prop_args_rel (fun (expr : aexp_stack) (val : nat) => aexp_stack_sem expr fenv stk (stk, val)) a_list vals0.
Proof.
  intros a_list args' fenv stk vals0 v H. remember (aexp_stk_size_inc_rel 1).
  revert vals0 stk fenv v.
  induction H; intros.
  - invs H0. invs H1. constructor.
  - invs H2. invs H3. invs H1. eapply RelArgsCons; eauto.
    eapply aexp_stack_increase_preserves_eval'; eauto.
Qed.

Lemma logic_stack_increase_preserves_eval :
  forall p p' fenv stk,
    transformed_prop_exprs (bexp_stk_size_inc_rel 1) p p' ->
    prop_rel (fun (boolexpr: bexp_stack) => bexp_stack_pure_rel boolexpr fenv) p ->
    eval_prop_rel (fun (boolexpr : bexp_stack) (boolval : bool) => bexp_stack_sem boolexpr fenv stk (stk, boolval)) p ->
    eval_prop_rel (fun (boolexpr : bexp_stack) (boolval : bool) => bexp_stack_sem boolexpr fenv (0 :: stk) (0 :: stk, boolval)) p'.
Proof.
  intros p p' fenv stk INC; dependent induction INC; intros PURE; intros; invs PURE.
  - econstructor.
  - invs H.
  - invs H0. econstructor.
    + pose proof (H4 := H3).
      eapply bexp_size_inc_preserves_purity in H3; [ | eassumption ].
      eapply bexp_stack_increase_preserves_eval; eassumption.
    + assumption.
  - invs H1.
    econstructor.
    + eapply bexp_stack_increase_preserves_eval; eassumption.
    + eapply bexp_stack_increase_preserves_eval; eassumption.
    + assumption.
  - invs H.
    econstructor.
    + eapply IHINC1; eauto.
    + eapply IHINC2; eauto.
  - invs H; econstructor; [eapply IHINC1; [reflexivity | .. ] | eapply IHINC2; [reflexivity | .. ]]; assumption.
  - invs H2.
    econstructor.
    1-3: eapply bexp_stack_increase_preserves_eval; eassumption; eassumption.
    assumption.
  - revert H. revert a_list'. induction a_list; intros.
    + invs H. invs H0. econstructor; [ | eassumption ].
      invs H5.
      econstructor.
    + invs H.
      invs H0. invs H6. invs PURE.
      econstructor.
      econstructor.
      eapply bexp_stack_increase_preserves_eval.
      eassumption.
      invs H4.
      assumption.
      eassumption.
      eapply bool_args_stack_increase_preserves_eval.
      eassumption.
      invs H4; eauto.
      eassumption.
      eassumption.
      (* assumption. *)
Qed.

Lemma logic_stack_increase_preserves_eval' :
  forall p p' fenv stk v,
    transformed_prop_exprs (bexp_stk_size_inc_rel 1) p p' ->
    bool_prop_wf p ->
    prop_rel (fun (boolexpr: bexp_stack) => bexp_stack_pure_rel boolexpr fenv) p ->
    eval_prop_rel (fun (boolexpr : bexp_stack) (boolval : bool) => bexp_stack_sem boolexpr fenv (v :: stk) (v :: stk, boolval)) p' ->
    eval_prop_rel (fun (boolexpr : bexp_stack) (boolval : bool) => bexp_stack_sem boolexpr fenv stk (stk, boolval)) p.
Proof.
  intros p p' fenv stk v H. revert v stk fenv.
  remember (bexp_stk_size_inc_rel 1).
  induction H; intros.
  - econstructor.
  - invs H1.
  - invs H1. invs H2. invs H0. econstructor; eauto.
    eapply bexp_stack_increase_preserves_eval'; eauto.
  - invs H1. invs H2. invs H3. econstructor; eauto.
    eapply bexp_stack_increase_preserves_eval'; eauto.
    eapply bexp_stack_increase_preserves_eval'; eauto. 
  - invs H1. invs H2. invs H3. econstructor; eauto.
  - invs H1. invs H2. invs H3.
    + eapply RelOrPropLeft; eauto.
    + eapply RelOrPropRight; eauto.
  - invs H2. invs H3. invs H4. 
    econstructor; eauto; eapply bexp_stack_increase_preserves_eval'; eauto.
  - invs H1. invs H2. invs H0.
    econstructor; eauto. eapply bool_args_stack_increase_preserves_eval'; eauto.
Qed.

Lemma nat_logic_stack_increase_preserves_eval :
  forall p p' fenv stk,
    transformed_prop_exprs (aexp_stk_size_inc_rel 1) p p' ->
    prop_rel (fun (natexpr: aexp_stack) => aexp_stack_pure_rel natexpr fenv) p ->
    eval_prop_rel (fun (natexpr : aexp_stack) (natval : nat) => aexp_stack_sem natexpr fenv stk (stk, natval)) p ->
    eval_prop_rel (fun (natexpr : aexp_stack) (natval : nat) => aexp_stack_sem natexpr fenv (0 :: stk) (0 :: stk, natval)) p'.
Proof.
  intros p p' fenv stk H. revert stk fenv.
  remember (aexp_stk_size_inc_rel 1).
  induction H; intros.
  - econstructor.
  - invs H0.
  - invs H0. invs H1. econstructor; eauto.
    eapply aexp_stack_increase_preserves_eval; eauto.
  - invs H1. invs H2. 
    econstructor; eauto; eapply aexp_stack_increase_preserves_eval; eauto.
  - invs H1. invs H2. econstructor; eauto.
  - invs H1. invs H2.
    + eapply RelOrPropLeft; eauto.
    + eapply RelOrPropRight; eauto.
  - invs H2. invs H3.
    econstructor; eauto; eapply aexp_stack_increase_preserves_eval; eauto.
  - invs H0. invs H1.
    econstructor; eauto. 
    eapply nat_args_stack_increase_preserves_eval; eauto.
Qed.

Lemma nat_logic_stack_increase_preserves_eval' :
  forall p p' fenv stk v,
    transformed_prop_exprs (aexp_stk_size_inc_rel 1) p p' ->
    nat_prop_wf p ->
    prop_rel (fun (natexpr: aexp_stack) => aexp_stack_pure_rel natexpr fenv) p ->
    eval_prop_rel (fun (natexpr : aexp_stack) (natval : nat) => aexp_stack_sem natexpr fenv (v :: stk) (v :: stk, natval)) p' ->
    eval_prop_rel (fun (natexpr : aexp_stack) (natval : nat) => aexp_stack_sem natexpr fenv stk (stk, natval)) p.
Proof.
  intros p p' fenv stk v H. revert fenv v stk.
  remember (aexp_stk_size_inc_rel 1).
  induction H; intros.
  - econstructor.
  - invs H1.
  - invs H0. invs H1. invs H2. econstructor; eauto.
    eapply aexp_stack_increase_preserves_eval'; eauto.
  - invs H1. invs H2. invs H3. 
    econstructor; eauto; eapply aexp_stack_increase_preserves_eval'; eauto.
  - invs H1. invs H2. invs H3. econstructor; eauto.
  - invs H1. invs H2. invs H3.
    + eapply RelOrPropLeft; eauto.
    + eapply RelOrPropRight; eauto.
  - invs H2. invs H3. invs H4.
    econstructor; eauto; eapply aexp_stack_increase_preserves_eval'; eauto.
  - invs H0. invs H1. invs H2.
    econstructor; eauto. 
    eapply nat_args_stack_increase_preserves_eval'; eauto.
Qed.
 
