From Coq Require Import String List Peano Arith Program.Equality.
From Imp_LangTrick Require Import Imp_LangLogHoare.
From Imp_LangTrick Require Import Imp_LangTrickLanguage.
From Imp_LangTrick Require Import EnvToStack.
From Imp_LangTrick Require Import StackLanguage.
From Imp_LangTrick Require Import Imp_LangLogProp.
From Imp_LangTrick Require Import LogicProp.
From Imp_LangTrick Require Import StackLangTheorems.
From Imp_LangTrick Require Import StackLogicBase.
From Imp_LangTrick Require Import LogicTranslationBase.
From Imp_LangTrick Require Import ImpVarMapTheorems.
From Imp_LangTrick Require Import CompilerCorrectHelpers.

Local Open Scope imp_langtrick_scope.



Lemma well_formed_preserved_by_aexp_update_backwards :
  forall (aexp aexp': aexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang)
    (WF_A: var_map_wf_wrt_aexp idents a)
    (IN: In x0 idents)
    (UPDATE: imp_lang_aexp_update_rel x0 a aexp aexp')
    (WF: var_map_wf_wrt_aexp idents aexp),
    var_map_wf_wrt_aexp idents aexp'.
Proof.
  intros aexp aexp' idents x0 a WF_A IN UPDATE WF.
  revert WF. revert UPDATE. revert IN. revert WF_A. revert aexp' idents x0 a. revert aexp.
  apply (aexp_Imp_Lang_ind2
           (fun aexp =>
              forall (aexp': aexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang)
                (WF_A: var_map_wf_wrt_aexp idents a)
    (IN: In x0 idents)
    (UPDATE: imp_lang_aexp_update_rel x0 a aexp aexp')
    (WF: var_map_wf_wrt_aexp idents aexp),
                var_map_wf_wrt_aexp idents aexp')); intros; invs UPDATE.
  - eassumption.
  - eassumption.
  - eassumption.
  - eassumption.
  - eapply var_map_wf_plus_imp_lang_backwards;
      eapply var_map_wf_plus_imp_lang_forwards in WF; destruct WF as (WF1 & WF2).
    + eapply H. eapply WF_A.
      eassumption.
      eassumption.
      eassumption.
    + eapply H0; [ eapply WF_A | eassumption .. ].
  - eapply var_map_wf_minus_imp_lang_backwards;
      eapply var_map_wf_minus_imp_lang_forwards in WF; destruct WF as (WF1 & WF2);
      (split; (idtac; solve [eapply H; [ eapply WF_A | eassumption .. ]
                            | eapply H0; [ eapply WF_A | eassumption .. ]])).
  - revert UPDATE. revert WF. revert H5.
    revert args'. induction H; intros.
    + invs UPDATE. invs H2.
      eassumption.
    + invs UPDATE. invs H4.
      eapply var_map_wf_app_imp_lang_first_and_rest with (aexp := x) (aexps := l) (f := f) in WF.
      destruct WF.
      eapply var_map_wf_app_imp_lang_first_and_rest_backward.
      assumption.
      split.
      * eapply H. eapply WF_A. eapply IN. eassumption. eassumption.
      * eapply IHForall.
        eassumption. eassumption. econstructor.
        assumption.
      * reflexivity.
Qed.                    

Lemma well_formed_preserved_by_aexp_update :
  forall (aexp aexp': aexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang)
    (WF_A: var_map_wf_wrt_aexp idents a)
    (IN: In x0 idents)
    (UPDATE: imp_lang_aexp_update_rel x0 a aexp aexp')
    (WF: var_map_wf_wrt_aexp idents aexp'),
    var_map_wf_wrt_aexp idents aexp.
Proof.
  intros aexp aexp' idents x0 a WF_A IN UPDATE WF.
  revert WF. revert UPDATE. revert IN. revert WF_A. revert aexp' idents x0 a. revert aexp.
  apply (aexp_Imp_Lang_ind2
           (fun aexp =>
              forall (aexp': aexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang)
                (WF_A: var_map_wf_wrt_aexp idents a)
    (IN: In x0 idents)
    (UPDATE: imp_lang_aexp_update_rel x0 a aexp aexp')
    (WF: var_map_wf_wrt_aexp idents aexp'),
                var_map_wf_wrt_aexp idents aexp)); intros.
  - invs UPDATE. eassumption.
  - invs UPDATE.
    + unfold_wf_aexp_in WF.
      destruct WF0 as (NODUP & _).
      eapply var_map_wf_var_imp_lang; eassumption.
    + assumption.
  - invs UPDATE.
    assumption.
  - invs UPDATE.
    eapply var_map_wf_plus_imp_lang_backwards.
    + eapply H.
      eapply WF_A.
      eassumption.
      eassumption.
      solve_var_map_wf.
    + eapply H0.
      eapply WF_A.
      eassumption.
      eassumption.
      solve_var_map_wf.
  - invs UPDATE. eapply var_map_wf_minus_imp_lang_backwards; [eapply H | eapply H0]; solve [ eapply WF_A | eassumption | solve_var_map_wf].
  - invs UPDATE.
    revert H5.
    revert UPDATE.
    revert WF. revert args'.
    induction H; intros.
    + invs H5. eassumption.
    + invs H5. eapply var_map_wf_app_imp_lang_backwards.
      * eapply H.
        eapply WF_A.
        eassumption.
        eassumption.
        eapply var_map_wf_app_imp_lang_first.
        ereflexivity.
        eassumption.
      * eapply var_map_wf_app_imp_lang_args_rest in WF.
        eapply IHForall.
        eassumption.
        econstructor.
        eassumption. assumption.
Qed.

Lemma var_map_wf_and_or_imp_lang_backwards :
  forall (b1 b2 b3: bexp_Imp_Lang) (idents: list ident),
    (b3 = (AND_Imp_Lang b1 b2) \/ b3 = (OR_Imp_Lang b1 b2)) ->
    var_map_wf_wrt_bexp idents b1 /\ var_map_wf_wrt_bexp idents b2 ->
    var_map_wf_wrt_bexp idents b3.
Proof.
  intros b1 b2 b3 idents DISJ [WF1 WF2].
  destruct DISJ.
  - subst. unfold_wf_bexp_in WF1. unfold_wf_bexp_in WF2.
    destruct WF.
    unfold_wf_bexp; intros.
    + apply prove_var_map_wf.
      assumption.
    + simpl in H1. rewrite H1 in H2.  eapply ListSet.set_union_iff in H2. destruct H2.
      * eapply A. reflexivity. assumption.
      * eapply A0. reflexivity. assumption.
    + eapply free_vars_in_bexp_has_variable. eassumption. assumption.
    + eapply find_index_rel_in_stronger.
      simpl in H1. rewrite H1 in H2. eapply ListSet.set_union_iff in H2. destruct H2.
      * eapply A. reflexivity. assumption.
      * eapply A0. reflexivity. assumption.
      * assumption.
  - subst. unfold_wf_bexp_in WF1. unfold_wf_bexp_in WF2.
    destruct WF.
    unfold_wf_bexp; intros.
    + apply prove_var_map_wf.
      assumption.
    + simpl in H1. rewrite H1 in H2.  eapply ListSet.set_union_iff in H2. destruct H2.
      * eapply A. reflexivity. assumption.
      * eapply A0. reflexivity. assumption.
    + eapply free_vars_in_bexp_has_variable. eassumption. assumption.
    + eapply find_index_rel_in_stronger.
      simpl in H1. rewrite H1 in H2. eapply ListSet.set_union_iff in H2. destruct H2.
      * eapply A. reflexivity. assumption.
      * eapply A0. reflexivity. assumption.
      * assumption.
Qed.

Lemma var_map_wf_leq_imp_lang_backwards :
  forall (b: bexp_Imp_Lang) (a1 a2: aexp_Imp_Lang) (idents: list ident),
    b = LEQ_Imp_Lang a1 a2 ->
    var_map_wf_wrt_aexp idents a1 /\ var_map_wf_wrt_aexp idents a2 ->
    var_map_wf_wrt_bexp idents b.
Proof.
  intros b a1 a2 idents LEQ [WF1 WF2].
  subst.
  unfold_wf_aexp_in WF1. unfold_wf_aexp_in WF2.
  destruct WF.
  unfold_wf_bexp; intros.
  - apply prove_var_map_wf.
    assumption.
  - simpl in H1. subst. eapply ListSet.set_union_iff in H2. destruct H2.
    + eapply A. reflexivity. assumption.
    + eapply A0. reflexivity. assumption.
  - simpl in H1. subst. eapply ListSet.set_union_iff in H2. destruct H2.
    + constructor. eapply free_vars_in_aexp_has_variable. reflexivity. assumption.
    + eapply BexpHasVarLeq__right. eapply free_vars_in_aexp_has_variable. reflexivity. assumption.
  - eapply find_index_rel_in_stronger; [ | assumption ].
    simpl in H1. subst. eapply ListSet.set_union_iff in H2. destruct H2.
    + eapply A. reflexivity. assumption.
    + eapply A0. reflexivity. assumption.
Qed.
  
Lemma well_formed_preserved_by_bexp_update :
  forall (bexp bexp': bexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang)
    (WF_A: var_map_wf_wrt_aexp idents a)
    (IN: In x0 idents)
    (UPDATE: imp_lang_bexp_update_rel x0 a bexp bexp')
    (WF: var_map_wf_wrt_bexp idents bexp'),
    var_map_wf_wrt_bexp idents bexp.
Proof.
  induction bexp; intros.
  - invs UPDATE. assumption.
  - invs UPDATE. assumption.
  - invs UPDATE. eapply var_map_wf_neg_imp_lang_forwards.
    reflexivity.
    eapply var_map_wf_neg_imp_lang in WF; [ | reflexivity ].
    eapply IHbexp.
    eassumption. eassumption.
    eassumption. assumption.
  - invs UPDATE. eapply var_map_wf_and_or_imp_lang_forwards in WF; [ | left; reflexivity ]. destruct WF as (WF1 & WF2). eapply var_map_wf_and_or_imp_lang_backwards.
    left. reflexivity. split.
    + eapply IHbexp1; eassumption.
    + eapply IHbexp2; eassumption.
  - invs UPDATE. eapply var_map_wf_and_or_imp_lang_forwards in WF; [ | right; reflexivity ]. destruct WF as (WF1 & WF2). eapply var_map_wf_and_or_imp_lang_backwards.
    right. reflexivity. split.
    + eapply IHbexp1; eassumption.
    + eapply IHbexp2; eassumption.
  - invs UPDATE. eapply var_map_wf_leq_imp_lang_forwards in WF; [ | reflexivity ].
    destruct WF as (WF1 & WF2).
    eapply var_map_wf_leq_imp_lang_backwards. reflexivity.
    split.
    + eapply well_formed_preserved_by_aexp_update.
      * eapply WF_A.
      * eassumption.
      * eassumption.
      * eassumption.
    + eapply well_formed_preserved_by_aexp_update with (aexp := a2) (a := a); eassumption.
Qed.


Lemma well_formed_preserved_by_logic_prop_update_args :
  forall (a_list a_list': list aexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs_args (V := nat) (fun aexp aexp' : aexp_Imp_Lang => imp_lang_aexp_update_rel x0 a aexp aexp') a_list a_list' ->
    prop_args_rel (V := nat) (var_map_wf_wrt_aexp idents) a_list' ->
    prop_args_rel (V := nat) (var_map_wf_wrt_aexp idents) a_list.
Proof.
  induction a_list; intros;
    match goal with
    | [ H : transformed_prop_exprs_args _ _ _ |- _ ] =>
        invs H;
        match goal with
        | [ H': prop_args_rel _ _ |- _ ] =>
            invs H'
        end
    end; econstructor.
  - eapply well_formed_preserved_by_aexp_update with (a := a0); try eassumption.
  - eapply IHa_list with (a := a0); try eassumption.
Qed.

Lemma well_formed_preserved_by_logic_prop_update_args_backwards :
  forall (a_list a_list': list aexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs_args (V := nat) (fun aexp aexp' : aexp_Imp_Lang => imp_lang_aexp_update_rel x0 a aexp aexp') a_list a_list' ->
    prop_args_rel (V := nat) (var_map_wf_wrt_aexp idents) a_list ->
    prop_args_rel (V := nat) (var_map_wf_wrt_aexp idents) a_list'.
Proof.
  induction a_list; intros;
    match goal with
    | [ H : transformed_prop_exprs_args _ _ _ |- _ ] =>
        invs H;
        match goal with
        | [ H': prop_args_rel _ _ |- _ ] =>
            invs H'
        end
    end; econstructor.
  - eapply well_formed_preserved_by_aexp_update_backwards with (a := a0); try eassumption.
  - eapply IHa_list with (a := a0); try eassumption.
Qed.
        
Lemma well_formed_preserved_by_logic_prop_update :
  forall (lp lp': LogicProp nat aexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs (fun aexp aexp' : aexp_Imp_Lang => imp_lang_aexp_update_rel x0 a aexp aexp') lp lp' ->
    prop_rel (var_map_wf_wrt_aexp idents) lp' ->
    prop_rel (var_map_wf_wrt_aexp idents) lp.
Proof.
  induction lp; intros;
    match goal with
    | [ H: transformed_prop_exprs _ _ _ |- _ ] =>
        invs H;
        match goal with
        | [ H': prop_rel _ _ |- _ ] =>
            invs H'
        end
    end.
  - econstructor.
  - econstructor.
  - econstructor. eapply well_formed_preserved_by_aexp_update with (a := a0); eassumption.
  - econstructor; eapply well_formed_preserved_by_aexp_update with (a := a); eassumption.
  - econstructor; [eapply IHlp1 | eapply IHlp2]; eassumption.
  - econstructor; [eapply IHlp1 | eapply IHlp2]; eassumption.
  - econstructor; eapply well_formed_preserved_by_aexp_update with (a := a); eassumption.
  - econstructor.
    eapply well_formed_preserved_by_logic_prop_update_args; eassumption.
Qed.

Lemma well_formed_preserved_by_logic_prop_update_backwards :
  forall (lp lp': LogicProp nat aexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs (fun aexp aexp' : aexp_Imp_Lang => imp_lang_aexp_update_rel x0 a aexp aexp') lp lp' ->
    prop_rel (var_map_wf_wrt_aexp idents) lp ->
    prop_rel (var_map_wf_wrt_aexp idents) lp'.
Proof.
  induction lp; intros;
    match goal with
    | [ H: transformed_prop_exprs _ _ _ |- _ ] =>
        invs H;
        match goal with
        | [ H': prop_rel _ _ |- _ ] =>
            invs H'
        end
    end.
  - econstructor.
  - econstructor.
  - econstructor. eapply well_formed_preserved_by_aexp_update_backwards with (a := a0); eassumption.
  - econstructor; eapply well_formed_preserved_by_aexp_update_backwards with (a := a); eassumption.
  - econstructor; [eapply IHlp1 | eapply IHlp2]; eassumption.
  - econstructor; [eapply IHlp1 | eapply IHlp2]; eassumption.
  - econstructor; eapply well_formed_preserved_by_aexp_update_backwards with (a := a); eassumption.
  - econstructor.
    eapply well_formed_preserved_by_logic_prop_update_args_backwards; eassumption.
Qed.

Lemma bool_well_formed_preserved_by_logic_prop_update_args :
  forall (b_list b_list': list bexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs_args (V := bool) (fun bexp bexp' : bexp_Imp_Lang => imp_lang_bexp_update_rel x0 a bexp bexp') b_list b_list' ->
    prop_args_rel (V := bool) (var_map_wf_wrt_bexp idents) b_list' ->
    prop_args_rel (V := bool) (var_map_wf_wrt_bexp idents) b_list.
Proof.
  induction b_list; intros;
    match goal with
    | [ H : transformed_prop_exprs_args _ _ _ |- _ ] =>
        invs H;
        match goal with
        | [ H': prop_args_rel _ _ |- _ ] =>
            invs H'
        end
    end; econstructor.
  - eapply well_formed_preserved_by_bexp_update; try eassumption.
  - eapply IHb_list; try eassumption.
Qed.


Lemma bool_well_formed_preserved_by_logic_prop_update :
  forall (lp lp': LogicProp bool bexp_Imp_Lang) (idents: list ident) (x0: ident) (a: aexp_Imp_Lang),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs (fun bexp bexp' : bexp_Imp_Lang => imp_lang_bexp_update_rel x0 a bexp bexp') lp lp' ->
    prop_rel (var_map_wf_wrt_bexp idents) lp' ->
    prop_rel (var_map_wf_wrt_bexp idents) lp.
Proof.
  induction lp; intros;
    match goal with
    | [ H: transformed_prop_exprs _ _ _ |- _ ] =>
        invs H;
        match goal with
        | [ H': prop_rel _ _ |- _ ] =>
            invs H'
        end
    end.
  - econstructor.
  - econstructor.
  - econstructor. eapply well_formed_preserved_by_bexp_update; eassumption.
  - econstructor; eapply well_formed_preserved_by_bexp_update; eassumption.
  - econstructor; [eapply IHlp1 | eapply IHlp2]; eassumption.
  - econstructor; [eapply IHlp1 | eapply IHlp2]; eassumption.
  - econstructor; eapply well_formed_preserved_by_bexp_update; eassumption.
  - econstructor.
    eapply bool_well_formed_preserved_by_logic_prop_update_args; eassumption.
Qed.

Lemma well_formed_preserved_by_log_prop_update :
  forall (d1 d: Imp_Lang_lp) (x: ident) (a: aexp_Imp_Lang) (idents: list ident),
    Imp_LangLogSubst.subst_AbsEnv_rel x a (AbsEnvLP d1) (AbsEnvLP d) ->
    In x idents ->
    var_map_wf_wrt_aexp idents a ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) (AbsEnvLP d) ->
    Imp_Lang_lp_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d1.
Proof.
  induction d1; intros.
  - invs H2. invs H. invs H8.
    invs H6.
    econstructor. eapply well_formed_preserved_by_logic_prop_update; try eassumption.
  - invs H2. invs H. invs H8. invs H6.
    econstructor.
    eapply bool_well_formed_preserved_by_logic_prop_update; try eassumption.
Qed.

Lemma well_formed_preserved_by_imp_lang_log_update :
  forall (l d: AbsEnv) (x: ident) (a: aexp_Imp_Lang) (idents: list ident),
    Imp_LangLogSubst.subst_AbsEnv_rel x a l d ->
    In x idents ->
    var_map_wf_wrt_aexp idents a ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) l.
Proof.
  induction l; intros.
  - invs H. invs H2. econstructor. eapply well_formed_preserved_by_log_prop_update; eassumption.
  - invs H. invs H2. econstructor; [eapply IHl1 | eapply IHl2]; try eassumption.
  - invs H. invs H2. econstructor; [eapply IHl1 | eapply IHl2]; try eassumption.
Qed.