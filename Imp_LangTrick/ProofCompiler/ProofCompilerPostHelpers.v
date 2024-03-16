From Coq Require Import Psatz Arith List Program.Equality String.
From Imp_LangTrick Require Import ProofCompiler StackLangTheorems ImpVarMap Imp_LangImpHigherOrderRel ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare Imp_LangImpHigherOrderRelTheorems LogicTranslationBase LogicTranslationAdequate Imp_LangTrickLanguage.
Import ProofCompiler.Tests.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.



Lemma fold_left_is_reverse_stronger :
  forall (s other: ListSet.set string),
    ListSet.set_fold_left
      (fun (acc: list string) (x: string) => x :: acc)
      s
      other = rev s ++ other.
Proof.
  induction s; intros; simpl.
  - reflexivity.
  - erewrite IHs.
    rewrite <- app_assoc.
    rewrite StackSubstitution.cons_is_append_singleton_list.
    reflexivity.
Qed.

Lemma fold_left_is_reverse :
  forall (s: ListSet.set string),
    ListSet.set_fold_left
      (fun (acc: list string) (x: string) => x :: acc)
      s
      nil = rev s.
Proof.
  intros. remember (rev s) as revs.
  rewrite app_nil_end in Heqrevs.
  subst. eapply fold_left_is_reverse_stronger.
Qed.

Lemma set_fold_left_of_set_union_identity :
  forall (s: ListSet.set string),
    NoDup s ->
    s = ListSet.set_fold_left (fun (acc: list string) (x: string) => x :: acc)
                              (ListSet.set_union string_dec (ListSet.empty_set string) s) nil.
Proof.
  induction s; intros.
  - simpl. reflexivity.
  - invs H.
    pose proof (H3' := H3).
    eapply IHs in H3'.
    simpl.
    rewrite no_dup_set_add_is_append.
    + rewrite fold_left_is_reverse. rewrite rev_app_distr.
      simpl. rewrite nil_set_union_is_reverse.
      rewrite rev_involutive. reflexivity. eassumption.
    + rewrite nil_set_union_is_reverse.
      econstructor.
      eapply not_in_preserved_by_reverse in H2. eassumption.
      eapply nodup_preserved_by_reverse in H3. eassumption.
      eassumption.
Qed.

Lemma containment_disjunction :
  forall (x: ident) (setA setB: ListSet.set ident) (idents: list ident),
    NoDup idents ->
    NoDup setA ->
    NoDup setB ->
    In x idents ->
    idents =
      ListSet.set_fold_left
        (fun (acc : list string) (x : string) => x :: acc)
        (ListSet.set_union string_dec setA
                           setB) nil ->
    In x setA \/ In x setB.
Proof.
  induction setA; intros.
  - right. pose proof (fold_left_containment_helper).
    specialize (H4 (ListSet.set_union string_dec nil setB) x).
    rewrite nil_set_union_is_reverse in H4; [ | eassumption ].
    rewrite fold_left_is_reverse in H4.
    rewrite rev_involutive in H4.
    rewrite nil_set_union_is_reverse in H3; [ | eassumption ].
    rewrite fold_left_is_reverse in H3.
    rewrite rev_involutive in H3. rewrite H3 in H2. eassumption.
  - rewrite fold_left_is_reverse_stronger in H3.
    rewrite <- app_nil_end in H3.
    rewrite H3 in H2.
    eapply in_preserved_by_reverse in H2.
    eapply ListSet.set_union_iff in H2.
    eassumption.
Qed.

Ltac exclude_ridiculous :=
  match goal with
  | [ H: ?x <> ?x |- _ ] =>
      let Heq := fresh "Heq" in
      assert (Heq: x = x) by reflexivity;
      eapply H in Heq; invs Heq
  | [ H: ?x <> ?y, H': ?x = ?y |- _ ] =>
      eapply H in H'; invs H'
  | [ H: ?x <> ?y, H': ?y = ?x |- _ ] =>
      symmetry in H'; eapply H in H'; invs H'
  end.

Lemma in_list_means_exists_index :
  forall (idents: list ident) (x: ident),
    In x idents ->
    exists k, (one_index_opt x idents = S k).
Proof.
  induction idents; intros.
  - invs H.
  - invs H.
    + exists 0. simpl.
      destruct (string_dec x x) eqn:Eq.
      reflexivity.
      exclude_ridiculous.
    + pose proof (string_dec x a).
      destruct H1.
      * exists 0. rewrite e. simpl. destruct (string_dec a a).
        reflexivity.
        exclude_ridiculous.
      * eapply IHidents in H0. destruct H0 as (k & H0).
        exists (S k).
        simpl.
        destruct (string_dec a x) eqn:Heq.
        clear Heq.
        exclude_ridiculous.
        rewrite H0. reflexivity.
Defined.

Lemma free_vars_in_imp_alternate :
  forall (idents: list ident) (i: imp_Imp_Lang) (x: ident),
    In x idents ->
    idents = construct_trans i ->
    imp_has_variable x i.
Proof.
  intros.
  rewrite H0 in H. unfold construct_trans in H.
  rewrite fold_left_is_reverse in H. eapply in_preserved_by_reverse in H.
  eapply free_vars_in_imp_has_variable in H; [ eassumption | ereflexivity].
Defined.

Ltac prove_nodup_finite :=
  match goal with
  | [ |- NoDup (?a :: ?alist) ] =>
      let Hin := fresh "Hin" in
      econstructor; [unfold not; intros Hin; invs Hin | prove_nodup_finite ]
  | [ |- NoDup nil ] =>
      econstructor
  end.

Lemma second_wf_proof :
  forall (idents: list string)
    (index : nat) (x : ident),
    0 <= index < Datatypes.length idents ->
    find_index_rel idents x (Some index) <->
      one_index_opt x idents = S index.
Proof.
  induction idents; intros index; induction index; split; intros.
  - invs H0.
  - simpl in H. invs H. invs H2.
  - invs H0.
  - invs H0.
  - invs H0.
    simpl. destruct (string_dec a a) eqn:Eqa; [ | exclude_ridiculous].
    reflexivity.
  - invs H0.
    destruct (string_dec a x) eqn:Eq.
    + subst. econstructor. reflexivity.
    + assert (one_index_opt x idents = 0).
      invs H2. reflexivity.
      unfold one_index_opt in H1.
      destruct idents. invs H1.
      destruct (string_dec s x) eqn:Eqs.
      invs H1.
      invs H1.
  - invs H0.
    simpl. destruct (string_dec a x); try exclude_ridiculous.
    f_equal.
    eapply IHidents.
    invs H. intuition.
    eassumption.
  - econstructor.
    simpl in H0. destruct (string_dec a x) eqn:Eqa.
    invs H0.
    unfold not; intros. symmetry in H1.  eapply n in H1. eassumption.
    simpl in H0. destruct (string_dec a x) eqn:Eqa.
    invs H0.
    invs H0. eapply IHidents.
    intuition. eassumption.
Defined.

Lemma well_formed_assign_param1 :
  imp_rec_rel (var_map_wf_wrt_imp ("z" :: nil)) ("z" <- PARAM_Imp_Lang 1).
Proof.
  pose proof (H := "z" = "z").
  econstructor. unfold_wf_imp; intros.
  * split; [ | split; [ | split]]; intros.
    -- econstructor. unfold not; intros. invs H0. econstructor.
    -- eapply second_wf_proof. eassumption.
    -- invs H0; [ | invs H1].
       exists 0. reflexivity.
    -- eapply free_vars_in_imp_alternate; eassumption.
  * econstructor. unfold_wf_aexp; intros.
    -- split; [ | split; [ | split ]]; intros.
       ++ prove_nodup_finite.
       ++ eapply second_wf_proof. eassumption.
       ++ eapply in_list_means_exists_index. eassumption.
       ++ eapply free_vars_in_imp_alternate; eassumption.
    -- simpl in H0. rewrite H0 in H1. invs H1.
    -- simpl in H0. rewrite H0 in H1. invs H1.
    -- simpl in H0. rewrite H0 in H1. invs H1.
    -- invs H0.
  * invs H0.
    -- eapply String.eqb_eq in H3. rewrite H3. econstructor. reflexivity.
    -- invs H3.
Qed.

Ltac prove_var_map_wf_wrt_bexp_no_vars_in_bexp :=
  unfold_wf_bexp; intros;
  [ | match goal with
      | [ H: ?idents = free_vars_bexp_src ?bexp,
            H': In ?x ?idents |- _ ] =>
          simpl in H;
          rewrite H in H';
          invs H'
      end .. ];
  split; [ | split; [ | split ]]; intros;
  [ prove_nodup_finite
  | eapply second_wf_proof; eassumption
  | eapply in_list_means_exists_index; eassumption
  | eapply free_vars_in_imp_alternate; eassumption ].

Ltac prove_var_map_wf_wrt_aexp_no_vars_in_aexp :=
  unfold_wf_aexp; intros;
  [ | match goal with
      | [ H: ?idents = free_vars_aexp_src ?bexp,
            H': In ?x ?idents |- _ ] =>
          simpl in H;
          rewrite H in H';
          invs H'
      end .. ];
  split; [ | split; [ | split ]]; intros;
  [ prove_nodup_finite
  | eapply second_wf_proof; eassumption
  | eapply in_list_means_exists_index; eassumption
  | eapply free_vars_in_imp_alternate; eassumption ].
