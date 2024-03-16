From Coq Require Import Arith Psatz List String.
From Imp_LangTrick Require Import Imp_LangLogSubst Imp_LangTrickLanguage Imp_LangLogProp Imp_LangLogicHelpers StackLangTheorems.
From Imp_LangTrick Require Import LogicPropTheorems LogicProp Imp_LangTrickTactics.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Lemma imp_lang_aexp_update_adequate_forward :
  forall (aexp aexp': aexp_Imp_Lang) (x: ident) (a: aexp_Imp_Lang),
    aexp' = imp_lang_aexp_update x a aexp ->
    imp_lang_aexp_update_rel x a aexp aexp'.
Proof.
  apply (aexp_Imp_Lang_ind2
           (fun aexp =>
              forall (aexp': aexp_Imp_Lang) (x: ident) (a: aexp_Imp_Lang),
                aexp' = imp_lang_aexp_update x a aexp ->
                imp_lang_aexp_update_rel x a aexp aexp'));
    intros; simpl in H; subst.
  - econstructor.
  - destruct_discrim_r (x =? x0)%string eqn:EQ;
      econstructor;
      try symmetry in EQ; try eassumption; try exclude_ridiculous.
  - econstructor.
  - simpl. econstructor; first [ eapply H | eapply H0]; eauto.
  - simpl. econstructor; first [ eapply H | eapply H0]; eauto.
  - revert x a. revert f. induction H; intros.
    + simpl. econstructor. econstructor.
    + simpl. econstructor. econstructor. eapply H. reflexivity.
      specialize (IHForall f x0 a).
      invs IHForall.
      assumption.
Defined.

Local Definition adequate_P (x: ident) (a: aexp_Imp_Lang) (aexp aexp': aexp_Imp_Lang): Prop :=
  aexp' = imp_lang_aexp_update x a aexp.

Local Definition adequate_P0 (x: ident) (a: aexp_Imp_Lang) (aexps aexps': list aexp_Imp_Lang): Prop :=
  aexps' = List.map (fun exp => imp_lang_aexp_update x a exp) aexps.



Lemma imp_lang_aexp_args_update_adequate_backward :
  imp_lang_aexp_args_update_rel_theorem adequate_P adequate_P0.
Proof.
  imp_lang_aexp_args_update_mutual_induction P P0 adequate_P adequate_P0; intros.
  - simpl. reflexivity.
  - reflexivity.
  - rewrite e. simpl. destruct_discrim_r (x =? x)%string eqn:EQ. reflexivity.
  - simpl. destruct_discrim_r (x =? x')%string eqn:EQ.
    reflexivity.
  - simpl. f_equal; eassumption.
  - simpl. f_equal; eassumption.
  - simpl. f_equal; try reflexivity.
    eassumption.
  - reflexivity.
  - simpl. rewrite H0. rewrite H. reflexivity.
Defined.

Lemma imp_lang_aexp_update_adequate_backward :
  forall (x : ident) (a aexp aexp' : aexp_Imp_Lang),
    imp_lang_aexp_update_rel x a aexp aexp' -> aexp' = imp_lang_aexp_update x a aexp.
Proof.
  pose proof (H:= imp_lang_aexp_args_update_adequate_backward).
  unfold imp_lang_aexp_args_update_rel_theorem,
    Imp_LangLogProp.imp_lang_aexp_args_update_rel_theorem_P,
    Imp_LangLogProp.imp_lang_aexp_args_update_rel_theorem_P0 in H.
  unfold adequate_P, adequate_P0 in H.
  destruct H as (AEXP & _).
  eapply AEXP.
Defined.

Lemma imp_lang_args_update_adequate_backward :     
  forall (x : ident) (a : aexp_Imp_Lang) (aexps aexps' : list aexp_Imp_Lang),
    imp_lang_args_update_rel x a aexps aexps' ->
    aexps' = map (fun exp : aexp_Imp_Lang => imp_lang_aexp_update x a exp) aexps.
Proof.
  pose proof (H:= imp_lang_aexp_args_update_adequate_backward).
  unfold imp_lang_aexp_args_update_rel_theorem,
    Imp_LangLogProp.imp_lang_aexp_args_update_rel_theorem_P,
    Imp_LangLogProp.imp_lang_aexp_args_update_rel_theorem_P0 in H.
  unfold adequate_P, adequate_P0 in H.
  destruct H as (_ & ARGS).
  eapply ARGS.
Defined.

Theorem imp_lang_aexp_update_adequacy :
  forall (x: ident) (a: aexp_Imp_Lang) (aexp aexp': aexp_Imp_Lang),
    aexp' = imp_lang_aexp_update x a aexp <->
      imp_lang_aexp_update_rel x a aexp aexp'.
Proof.
  split; intros;
    first [ eapply imp_lang_aexp_update_adequate_forward
          | eapply imp_lang_aexp_update_adequate_backward];
    eassumption.
Defined.

Lemma imp_lang_args_update_adequate_forward :
  forall (aexps aexps': list aexp_Imp_Lang) (x: ident) (a: aexp_Imp_Lang),
    aexps' = map (fun exp : aexp_Imp_Lang => imp_lang_aexp_update x a exp) aexps ->
    imp_lang_args_update_rel x a aexps aexps'.
Proof.
  induction aexps; intros; simpl in H; subst; econstructor.
  - eapply imp_lang_aexp_update_adequacy. reflexivity.
  - eapply IHaexps. reflexivity.
Defined.

Theorem imp_lang_args_update_adequacy :
  forall (x: ident) (a: aexp_Imp_Lang) (aexps aexps': list aexp_Imp_Lang),
    aexps' = map (fun exp : aexp_Imp_Lang => imp_lang_aexp_update x a exp) aexps <->
      imp_lang_args_update_rel x a aexps aexps'.
Proof.
  split;
    intros;
    first [ eapply imp_lang_args_update_adequate_backward
          | eapply imp_lang_args_update_adequate_forward];
    eauto.
Defined.

                              


Lemma imp_lang_bexp_update_adequate_forward :
  forall (bexp bexp': bexp_Imp_Lang) (x: ident) (a: aexp_Imp_Lang),
    bexp' = imp_lang_bexp_update x a bexp ->
    imp_lang_bexp_update_rel x a bexp bexp'.
Proof.
  induction bexp; intros; simpl in H; subst; econstructor;
    first [ eapply IHbexp
          | eapply IHbexp1
          | eapply IHbexp2
          | eapply imp_lang_aexp_update_adequacy];
    eauto.
Defined.


Lemma imp_lang_bexp_update_adequate_backward :
  forall (bexp bexp': bexp_Imp_Lang) (x: ident) (a: aexp_Imp_Lang),
    imp_lang_bexp_update_rel x a bexp bexp' ->
    bexp' = imp_lang_bexp_update x a bexp.
Proof.
  induction bexp; intros; invs H; simpl; try eauto; f_equal;
    first [ eapply IHbexp
          | eapply IHbexp1
          | eapply IHbexp2
          | eapply imp_lang_aexp_update_adequacy];
    eauto.
Defined.

Theorem imp_lang_bexp_update_adequacy :
  forall (bexp bexp': bexp_Imp_Lang) (x: ident) (a: aexp_Imp_Lang),
    bexp' = imp_lang_bexp_update x a bexp <->
      imp_lang_bexp_update_rel x a bexp bexp'.
Proof.
  split; intros;
    first [ eapply imp_lang_bexp_update_adequate_forward
          | eapply imp_lang_bexp_update_adequate_backward];
    eassumption.
Defined.

Lemma imp_lang_lp_subst_adequate_forward :
  forall (d d': Imp_Lang_lp) (x: ident) (a: aexp_Imp_Lang),
    d' = subst_Imp_Lang_lp x a d ->
    subst_Imp_Lang_lp_rel x a d d'.
Proof.
  induction d'; intros.
  - destruct d; [ | simpl in H; invs H ].
    econstructor.
    simpl in H. inversion H.
    eapply transform_prop_exprs_adequacy_forward.
    eapply imp_lang_aexp_update_adequacy.
    reflexivity.
  - destruct d; [simpl in H; invs H | ].
    econstructor. simpl in H. inversion H.
    eapply transform_prop_exprs_adequacy_forward.
    intros.
    eapply imp_lang_bexp_update_adequacy.
    reflexivity.
Defined.



Lemma imp_lang_log_subst_adequate_forward :
  forall (d d': AbsEnv) (x: ident) (a: aexp_Imp_Lang),
    d' = subst_AbsEnv x a d ->
    subst_AbsEnv_rel x a d d'.
Proof.
  induction d; intros; simpl in H; rewrite H.
  - econstructor.
    eapply imp_lang_lp_subst_adequate_forward.
    reflexivity.
  - econstructor; first [ eapply IHd1 | eapply IHd2 ]; eauto.
  - econstructor; first [ eapply IHd1 | eapply IHd2 ]; eauto.
Defined.


Lemma imp_lang_lp_subst_adequate_backward :
  forall (d d': Imp_Lang_lp) (x: ident) (a: aexp_Imp_Lang),
    subst_Imp_Lang_lp_rel x a d d' ->
    d' = subst_Imp_Lang_lp x a d.
Proof.
  induction d; intros; invs H; simpl.
  - eapply transform_prop_exprs_adequacy_backward in H3.
    + f_equal. rewrite H3. eauto.
    + intros; split; intros; eapply imp_lang_aexp_update_adequacy; eauto.
  - eapply transform_prop_exprs_adequacy_backward in H3.
    + f_equal. rewrite H3. eauto.
    + intros; split; intros; eapply imp_lang_bexp_update_adequacy; eauto.
Defined.

Lemma imp_lang_log_subst_adequate_backward :
  forall (d d': AbsEnv) (x: ident) (a: aexp_Imp_Lang),
    subst_AbsEnv_rel x a d d' ->
    d' = subst_AbsEnv x a d.
Proof.
  induction d; intros; invs H; simpl.
  - eapply imp_lang_lp_subst_adequate_backward in H3. subst. eauto.
  - eapply IHd1 in H4. eapply IHd2 in H6. subst. eauto.
  - eapply IHd1 in H4. eapply IHd2 in H6. subst. eauto. 
Defined.

Theorem imp_lang_lp_subst_adequacy :
  forall (d d': Imp_Lang_lp) (x: ident) (a: aexp_Imp_Lang),
    d' = subst_Imp_Lang_lp x a d <->
      subst_Imp_Lang_lp_rel x a d d'.
Proof.
  split; intros;
    first [ eapply imp_lang_lp_subst_adequate_forward
          | eapply imp_lang_lp_subst_adequate_backward ];
    eauto.
Defined.

Theorem imp_lang_log_subst_adequacy :
  forall (d d': AbsEnv) (x: ident) (a: aexp_Imp_Lang),
    d' = subst_AbsEnv x a d <->
      subst_AbsEnv_rel x a d d'.
Proof.
  split; intros;
    first [ eapply imp_lang_log_subst_adequate_forward
          | eapply imp_lang_log_subst_adequate_backward ];
    eauto.
Defined.
                      
