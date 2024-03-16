From Coq Require Import String List Psatz Peano Program.Equality.
From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage EnvToStack StackLangTheorems.
From Imp_LangTrick Require Import Imp_LangTrickSemanticsMutInd ImpVarMap ImpVarMapTheorems.
From Imp_LangTrick Require Import LogicTranslationBase Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems.
From Imp_LangTrick Require Import CompilerCorrectHelpers.

Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

From Imp_LangTrick Require Import ProofSubstitution.
Lemma var_map_wf_wrt_bexp_subset_stronger :
  forall (b: bexp_Imp_Lang) (idents idents': list ident),
    (forall x,
        In x idents ->
        In x idents') ->
    NoDup idents' ->
    NoDup idents ->
    var_map_wf_wrt_bexp idents b ->
    var_map_wf_wrt_bexp idents' b.
Proof.
  induction b; intros.
  - apply true_imp_lang_always_well_formed. assumption.
  - apply false_imp_lang_always_well_formed. assumption.
  - eapply var_map_wf_neg_imp_lang_forwards. reflexivity.
    eapply var_map_wf_neg_imp_lang in H2; [ | reflexivity ].
    eapply IHb; eassumption.
  - eapply var_map_wf_and_or_imp_lang_backwards. left. reflexivity. eapply var_map_wf_and_or_imp_lang_forwards in H2; [ | left; reflexivity ].
    destruct H2. split.
    + eapply IHb1; eassumption.
    + eapply IHb2; eassumption.
  - eapply var_map_wf_and_or_imp_lang_backwards. right. reflexivity. eapply var_map_wf_and_or_imp_lang_forwards in H2; [ | right; reflexivity ].
    destruct H2. split.
    + eapply IHb1; eassumption.
    + eapply IHb2; eassumption.
  - eapply var_map_wf_leq_imp_lang_backwards. reflexivity. eapply var_map_wf_leq_imp_lang_forwards in H2; [ | reflexivity ]. destruct H2.
    split; eapply var_map_wf_wrt_aexp_subset_stronger; eassumption.
Qed.

Lemma var_map_wf_wrt_bexp_subset :
  forall (idents: list ident) (b: bexp_Imp_Lang),
    (forall x,
        In x (free_vars_bexp_src b) ->
        In x idents) ->
    NoDup idents ->
    var_map_wf_wrt_bexp idents b.
Proof.
  intros. eapply var_map_wf_wrt_bexp_subset_stronger. eassumption. assumption. eapply nodup_free_vars_bexp.
  eapply var_map_wf_wrt_bexp_self. reflexivity.
Qed.

Lemma var_map_wf_bexp_nil_trivial :
  forall (b: bexp_Imp_Lang),
    (forall x,
        In x (free_vars_bexp_src b) ->
        In x nil) ->
    var_map_wf_wrt_bexp nil b.
Proof.
  intros. eapply var_map_wf_wrt_bexp_subset. eapply H. constructor.
Qed.

Lemma fold_left_containment_helper_forward :
  forall (ident_set : ListSet.set ident) (x0 : ident),
    In x0 (ListSet.set_fold_left (fun (acc : list string) (x : string) => x :: acc) ident_set nil) -> In x0 ident_set.
Proof.
  intros. eapply fold_left_containment_helper. eassumption.
Qed.

Lemma fold_left_containment_helper_backward :
  forall (ident_set : ListSet.set ident) (x0 : ident),
    In x0 ident_set ->
    In x0 (ListSet.set_fold_left (fun (acc : list string) (x : string) => x :: acc) ident_set nil).
Proof.
  intros. eapply fold_left_containment_helper in H. assumption.
Qed.


Lemma var_map_wf_wrt_imp_subset' :
  forall (i: imp_Imp_Lang) (idents: list ident),
    imp_forall_relation_on_aexps_bexps (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) i ->
    forall (idents': list ident),
    (forall x,
        In x idents ->
        In x idents') ->
    NoDup idents ->
    NoDup idents' ->
    imp_forall_relation_on_aexps_bexps (var_map_wf_wrt_aexp idents') (var_map_wf_wrt_bexp idents') i.
Proof.
  intros i idents FORALL. dependent induction FORALL; intros.
  - constructor.
  - constructor.
    eapply var_map_wf_wrt_aexp_subset_stronger. eassumption. assumption. assumption. assumption.
  - constructor.
    + eapply IHFORALL1; try eassumption. reflexivity. reflexivity.
    + eapply IHFORALL2; try eassumption; reflexivity.
  - constructor.
    + eapply var_map_wf_wrt_bexp_subset_stronger; eassumption.
    + eapply IHFORALL1; try eassumption; reflexivity.
    + eapply IHFORALL2; try eassumption; reflexivity.
  - constructor.
    + eapply var_map_wf_wrt_bexp_subset_stronger; eassumption.
    + eapply IHFORALL; try eassumption; reflexivity.
Qed.

Lemma var_map_wf_imp_self :
  forall (idents: list ident) (i: imp_Imp_Lang),
  forall (ID: idents = construct_trans i),
    var_map_wf_wrt_imp idents i.
Proof.
  unfold_wf_imp; intros.
  - split; [ | split; [ | split ]]; intros; subst.
    + apply nodup_construct_trans.
    + split; intros.
      * eapply find_index_rel_implication. assumption.
      * apply find_index_rel_help in H0; assumption.
    + apply in_idents_one_index_opt in H. destruct H.
      destruct x0.
      * eapply one_index_opt_not_0 in H. invs H.
      * exists x0. assumption.
      * apply nodup_construct_trans.
    + rewrite H0 in H. unfold construct_trans in H.
      pose proof (fold_left_containment_helper). specialize (H1 (free_vars_imp_src imp) x).
      destruct H1. apply H1 in H. eapply free_vars_in_imp_has_variable. ereflexivity. assumption.
  - specialize (nodup_construct_trans i). intros. revert ID. revert idents. induction i; intros.
    + constructor.
      remember (free_vars_bexp_src b) as FVb.
      pose proof (ID' := ID).
      unfold construct_trans in ID. simpl in ID.
      assert (forall x, In x (free_vars_bexp_src b) ->
                   In x idents).
      intros.
      rewrite ID. eapply fold_left_containment_helper.
      eapply ListSet.set_union_intro1. assumption.
      eapply var_map_wf_wrt_bexp_subset; try eassumption.
      rewrite ID'. assumption.
      specialize (IHi1 (nodup_construct_trans i1) (construct_trans i1) eq_refl).
      eapply var_map_wf_wrt_imp_subset' with (idents' := idents) in IHi1.
      assumption.
      intros. unfold construct_trans in H0. eapply fold_left_containment_helper_forward in H0.
      rewrite ID. unfold construct_trans. eapply fold_left_containment_helper_backward. simpl.
      eapply ListSet.set_union_intro2. eapply ListSet.set_union_intro1. assumption.
      apply nodup_construct_trans. rewrite ID. assumption.
      specialize (IHi2 (nodup_construct_trans i2) (construct_trans i2) (eq_refl)).
      eapply var_map_wf_wrt_imp_subset' with (idents' := idents) in IHi2; try assumption.
      intros. rewrite ID. unfold construct_trans in *.
      eapply fold_left_containment_helper_forward in H0. eapply fold_left_containment_helper_backward. simpl.
      eapply ListSet.set_union_intro2. eapply ListSet.set_union_intro2. assumption.
      eapply nodup_construct_trans. rewrite ID. assumption.
    + constructor.
    + pose proof (ID' := ID).
      unfold construct_trans in ID. simpl in ID. constructor.
      * assert (forall x, In x (free_vars_bexp_src b) -> In x idents).
        intros. rewrite ID. eapply fold_left_containment_helper_backward. eapply ListSet.set_union_intro2. assumption.
        eapply var_map_wf_wrt_bexp_subset; try eassumption.
        rewrite ID'. assumption.
      * revert ID'. subst. intros. specialize (IHi (nodup_construct_trans i) (construct_trans i) eq_refl).
        apply var_map_wf_wrt_imp_subset' with (idents' := (construct_trans (WHILE_Imp_Lang b i))) in IHi; try assumption.
        intros. unfold construct_trans in *. apply fold_left_containment_helper_forward in H0. apply fold_left_containment_helper_backward.
        simpl. eapply ListSet.set_union_intro1. assumption.
        eapply nodup_construct_trans.
    + pose proof (ID' := ID).
      unfold construct_trans in ID. constructor.
      rewrite ID. assert (forall x, In x (free_vars_aexp_src a) -> In x idents).
      intros. rewrite ID. apply fold_left_containment_helper_backward. simpl. apply ListSet.set_add_intro1. assumption.
      eapply var_map_wf_wrt_aexp_subset.
      rewrite ID in H0. assumption.
      rewrite <- ID. rewrite ID'. apply nodup_construct_trans.
    + pose proof (ID' := ID).
      unfold construct_trans in ID. simpl in ID. constructor.
      * assert (forall x, In x (free_vars_imp_src i1) -> In x idents).
        intros. rewrite ID. eapply fold_left_containment_helper_backward. eapply ListSet.set_union_intro1. assumption.
        specialize (IHi1 (nodup_construct_trans i1) (construct_trans i1) eq_refl).
        eapply var_map_wf_wrt_imp_subset' in IHi1. eassumption.
        intros. eapply H0. unfold construct_trans in H1. eapply fold_left_containment_helper_forward in H1. assumption.
        apply nodup_construct_trans.  rewrite ID'. assumption.
      * assert (forall x, In x (free_vars_imp_src i2) -> In x idents).
        -- intros. rewrite ID. apply fold_left_containment_helper_backward. apply ListSet.set_union_intro2. assumption.
        -- specialize (IHi2 (nodup_construct_trans i2) (construct_trans i2) eq_refl).
           eapply var_map_wf_wrt_imp_subset' in IHi2. eassumption.
           intros. apply H0. unfold construct_trans in H1. apply fold_left_containment_helper_forward in H1. assumption.
           eapply nodup_construct_trans. rewrite ID'. assumption.
  - rewrite ID. unfold construct_trans. apply fold_left_containment_helper_backward. eapply free_vars_in_imp_has_variable.
    reflexivity. assumption.
Qed.

Lemma var_map_wf_wrt_imp_subset :
  forall (i: imp_Imp_Lang) (idents: list ident),
    var_map_wf_wrt_imp idents i ->
    forall (idents': list ident),
      (forall x,
          In x idents ->
          In x idents') ->
      NoDup idents' ->
      var_map_wf_wrt_imp idents' i.
Proof.
  intros. unfold_wf_imp_in H; unfold_wf_imp; intros.
  - eapply prove_var_map_wf. assumption.
  - destruct WF as (NODUP & WF).
    eapply var_map_wf_wrt_imp_subset'; eassumption.
  - eapply H0. eapply WF''. assumption. 
Qed.


      

Lemma var_map_wf_wrt_imp_subset_imp_rec_rel :
  forall (i: imp_Imp_Lang) (idents: list ident),
    imp_rec_rel (var_map_wf_wrt_imp idents) i ->
    forall (idents': list ident),
      (forall x,
          In x idents ->
          In x idents') ->
      NoDup idents ->
      NoDup idents' ->
      imp_rec_rel (var_map_wf_wrt_imp idents') i.
Proof.
  induction i; intros; invs H.
  - constructor.
    + eapply IHi1; eassumption.
    + eapply IHi2; eassumption.
    + eapply var_map_wf_wrt_imp_subset; eassumption.
  - constructor. eapply var_map_wf_wrt_imp_subset; eassumption.
  - constructor.
    + eapply IHi; eassumption.
    + eapply var_map_wf_wrt_imp_subset; eassumption.
  - constructor. eapply var_map_wf_wrt_imp_subset; eassumption.
  - constructor.
    + eapply IHi1; eassumption.
    + eapply IHi2; eassumption.
    + eapply var_map_wf_wrt_imp_subset; eassumption.
Qed.

Lemma var_map_wf_imp_self_imp_rec_rel :
  forall (i: imp_Imp_Lang) (idents: list ident),
  forall (ID: construct_trans i = idents),
    imp_rec_rel (var_map_wf_wrt_imp idents) i.
Proof.
  induction i; intros; pose proof (ID' := ID); unfold construct_trans in ID; simpl in ID.
  - constructor.
    + specialize (IHi1 (construct_trans i1) eq_refl).
      eapply var_map_wf_wrt_imp_subset_imp_rec_rel with (idents := construct_trans i1).
      * assumption.
      * intros. rewrite <- ID. unfold construct_trans in H. eapply fold_left_containment_helper_forward in H.
        eapply fold_left_containment_helper_backward. eapply ListSet.set_union_intro2. eapply ListSet.set_union_intro1. assumption.
      * eapply nodup_construct_trans.
      * rewrite <- ID'. eapply nodup_construct_trans.
    + specialize (IHi2 (construct_trans i2) eq_refl).
      eapply var_map_wf_wrt_imp_subset_imp_rec_rel with (idents := construct_trans i2).
      * assumption.
      * intros. rewrite <- ID. unfold construct_trans in H. eapply fold_left_containment_helper_forward in H. eapply fold_left_containment_helper_backward. repeat eapply ListSet.set_union_intro2. eassumption.
      * eapply nodup_construct_trans.
      * rewrite <- ID'. eapply nodup_construct_trans.
    + rewrite <- ID'. eapply var_map_wf_imp_self. reflexivity.
  - constructor.
    eapply var_map_wf_imp_self. rewrite ID'. reflexivity.
  - constructor.
    + specialize (IHi (construct_trans i) eq_refl).
      eapply var_map_wf_wrt_imp_subset_imp_rec_rel with (idents := construct_trans i).
      * assumption.
      * intros. rewrite <- ID. unfold construct_trans in H. eapply fold_left_containment_helper_forward in H. eapply fold_left_containment_helper_backward. repeat eapply ListSet.set_union_intro1. eassumption.
      * eapply nodup_construct_trans.
      * rewrite <- ID'. eapply var_map_wf_imp_self. reflexivity.
    + eapply var_map_wf_imp_self. rewrite ID'. reflexivity.
  - constructor. eapply var_map_wf_imp_self. rewrite <- ID'. reflexivity.
  - constructor.
    + specialize (IHi1 (construct_trans i1) eq_refl).
      eapply var_map_wf_wrt_imp_subset_imp_rec_rel with (idents := construct_trans i1).
      * assumption.
      * intros. rewrite <- ID. unfold construct_trans in H. eapply fold_left_containment_helper_forward in H. eapply fold_left_containment_helper_backward. repeat eapply ListSet.set_union_intro1. eassumption.
      * eapply nodup_construct_trans.
      * rewrite <- ID'. eapply var_map_wf_imp_self. reflexivity.
    + specialize (IHi2 (construct_trans i2) eq_refl).
      eapply var_map_wf_wrt_imp_subset_imp_rec_rel with (idents := construct_trans i2).
      * assumption.
      * intros. rewrite <- ID. unfold construct_trans in H. eapply fold_left_containment_helper_forward in H. eapply fold_left_containment_helper_backward. repeat eapply ListSet.set_union_intro2. eassumption.
      * eapply nodup_construct_trans.
      * rewrite <- ID'. eapply var_map_wf_imp_self. reflexivity.
    + eapply var_map_wf_imp_self. rewrite ID'. reflexivity.
Qed.

Lemma var_map_wf_aexp_bexp_forall_i_nil_trivial :
  forall (i: imp_Imp_Lang),
    construct_trans i = nil ->
    imp_forall_relation_on_aexps_bexps (var_map_wf_wrt_aexp nil) (var_map_wf_wrt_bexp nil) i.
Proof.
  induction i; intros.
  - unfold construct_trans in H. eapply list_set_fold_left_other_is_nil in H.  simpl in H. eapply set_union_nil in H. destruct H. eapply set_union_nil in H0. destruct H0.
    2: apply nodup_free_vars_imp.
    2: apply set_union_no_dups; eapply nodup_free_vars_imp.
    constructor.    eapply var_map_wf_wrt_bexp_subset_stronger with (idents := (free_vars_bexp_src b)).
    intros. rewrite H in H2. assumption. 
    constructor.
    eapply nodup_free_vars_bexp. eapply var_map_wf_wrt_bexp_self. reflexivity.
    eapply IHi1. unfold construct_trans in *. simpl in H.
    rewrite H0. reflexivity.
    eapply IHi2. unfold construct_trans in *. rewrite H1. reflexivity.
  - constructor.
  - unfold construct_trans in H. eapply list_set_fold_left_other_is_nil in H. simpl in H. eapply set_union_nil in H; [ | eapply nodup_free_vars_bexp ]. destruct H.
    constructor.
    + eapply var_map_wf_bexp_nil_trivial. intros. rewrite H0 in H1. assumption.
    + eapply IHi. unfold construct_trans. rewrite H. reflexivity.
  - unfold construct_trans in H. constructor.
    simpl in H. eapply list_set_fold_left_other_is_nil in H.
    pose proof (ListSet.set_add_not_empty string_dec x (free_vars_aexp_src a)).
    change (ListSet.empty_set string) with (nil (A := string)) in H0.
    congruence.
  - unfold construct_trans in H. eapply list_set_fold_left_other_is_nil in H. simpl in H. eapply set_union_nil in H; [ | eapply nodup_free_vars_imp ]. destruct H.
    constructor.
    + eapply IHi1. unfold construct_trans. rewrite H. reflexivity.
    + eapply IHi2. unfold construct_trans. rewrite H0. reflexivity.
Qed.
      

Lemma var_map_wf_imp_nil_trivial :
  forall (i: imp_Imp_Lang),
    construct_trans i = nil ->
    imp_rec_rel (var_map_wf_wrt_imp nil) i.
Proof.
  intros.
  induction i; intros.
  - constructor; try assumption; unfold construct_trans in H; simpl in H.
    apply list_set_fold_left_other_is_nil in H. apply set_union_nil in H. destruct H. apply set_union_nil in H0. destruct H0.
    apply construct_trans_nil in H0. apply IHi1 in H0. assumption.
    apply nodup_free_vars_imp.
    apply set_union_no_dups. apply nodup_free_vars_imp.
    apply list_set_fold_left_other_is_nil in H. apply set_union_nil in H. destruct H. apply set_union_nil in H0. destruct H0.
    apply construct_trans_nil in H1. apply IHi2 in H1. assumption.
    apply nodup_free_vars_imp. apply set_union_no_dups. apply nodup_free_vars_imp.
    apply list_set_fold_left_other_is_nil in H; destruct_set_unions H; [ | apply nodup_free_vars_imp | apply set_union_no_dups; apply nodup_free_vars_imp ].
    unfold_wf_imp.
    + split; [ | split; [ | split ]]; intros.
      * constructor.
      * simpl in H. invs H0. invs H2.
      * invs H0.
      * invs H0.
    + constructor.
      * eapply var_map_wf_wrt_bexp_self. symmetry in H. assumption.
      * eapply var_map_wf_wrt_imp_subset'. shelve.
        shelve.
        eapply (nodup_construct_trans i1).
        constructor.
        Unshelve.
        unfold construct_trans. rewrite Ho. simpl.
        eapply var_map_wf_aexp_bexp_forall_i_nil_trivial.
        unfold construct_trans. rewrite Ho. reflexivity.
        intros. unfold construct_trans in H0. rewrite Ho in H0. invs H0.
      * eapply var_map_wf_aexp_bexp_forall_i_nil_trivial.
        unfold construct_trans. rewrite Ho0. reflexivity.
    + intros. eapply free_vars_in_imp_has_variable in H0; [ | reflexivity ].
      simpl in H0. rewrite H, Ho, Ho0 in H0. invs H0.
  - constructor. eapply var_map_wf_imp_self. symmetry. assumption.
  - constructor.
    + eapply IHi. unfold construct_trans in *. eapply list_set_fold_left_other_is_nil in H. simpl in H. eapply set_union_nil in H. destruct H. rewrite H. reflexivity.
      eapply nodup_free_vars_bexp.
    + eapply var_map_wf_imp_self. symmetry. assumption.
  - constructor. eapply var_map_wf_imp_self. symmetry. assumption.
  - unfold construct_trans in H. eapply list_set_fold_left_other_is_nil in H. simpl in H. eapply set_union_nil in H; [ | eapply nodup_free_vars_imp ]. destruct H.
    constructor.
    + eapply IHi1. unfold construct_trans. rewrite H. reflexivity.
    + eapply IHi2. unfold construct_trans. rewrite H0. reflexivity.
    + eapply var_map_wf_imp_self.
      unfold construct_trans. simpl. rewrite H, H0. reflexivity.
Qed.
