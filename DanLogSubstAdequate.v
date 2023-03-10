From Coq Require Import Arith Psatz List String.
From DanTrick Require Import DanLogSubst DanTrickLanguage DanLogProp DanLogicHelpers StackLangTheorems.
From DanTrick Require Import LogicPropTheorems LogicProp DanTrickTactics.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Lemma dan_aexp_update_adequate_forward :
  forall (aexp aexp': aexp_Dan) (x: ident) (a: aexp_Dan),
    aexp' = dan_aexp_update x a aexp ->
    dan_aexp_update_rel x a aexp aexp'.
Proof.
  apply (aexp_Dan_ind2
           (fun aexp =>
              forall (aexp': aexp_Dan) (x: ident) (a: aexp_Dan),
                aexp' = dan_aexp_update x a aexp ->
                dan_aexp_update_rel x a aexp aexp'));
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

Local Definition adequate_P (x: ident) (a: aexp_Dan) (aexp aexp': aexp_Dan): Prop :=
  aexp' = dan_aexp_update x a aexp.

Local Definition adequate_P0 (x: ident) (a: aexp_Dan) (aexps aexps': list aexp_Dan): Prop :=
  aexps' = List.map (fun exp => dan_aexp_update x a exp) aexps.



Lemma dan_aexp_args_update_adequate_backward :
  dan_aexp_args_update_rel_theorem adequate_P adequate_P0.
Proof.
  dan_aexp_args_update_mutual_induction P P0 adequate_P adequate_P0; intros.
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

Lemma dan_aexp_update_adequate_backward :
  forall (x : ident) (a aexp aexp' : aexp_Dan),
    dan_aexp_update_rel x a aexp aexp' -> aexp' = dan_aexp_update x a aexp.
Proof.
  pose proof (H:= dan_aexp_args_update_adequate_backward).
  unfold dan_aexp_args_update_rel_theorem,
    DanLogProp.dan_aexp_args_update_rel_theorem_P,
    DanLogProp.dan_aexp_args_update_rel_theorem_P0 in H.
  unfold adequate_P, adequate_P0 in H.
  destruct H as (AEXP & _).
  eapply AEXP.
Defined.

Lemma dan_args_update_adequate_backward :     
  forall (x : ident) (a : aexp_Dan) (aexps aexps' : list aexp_Dan),
    dan_args_update_rel x a aexps aexps' ->
    aexps' = map (fun exp : aexp_Dan => dan_aexp_update x a exp) aexps.
Proof.
  pose proof (H:= dan_aexp_args_update_adequate_backward).
  unfold dan_aexp_args_update_rel_theorem,
    DanLogProp.dan_aexp_args_update_rel_theorem_P,
    DanLogProp.dan_aexp_args_update_rel_theorem_P0 in H.
  unfold adequate_P, adequate_P0 in H.
  destruct H as (_ & ARGS).
  eapply ARGS.
Defined.

Theorem dan_aexp_update_adequacy :
  forall (x: ident) (a: aexp_Dan) (aexp aexp': aexp_Dan),
    aexp' = dan_aexp_update x a aexp <->
      dan_aexp_update_rel x a aexp aexp'.
Proof.
  split; intros;
    first [ eapply dan_aexp_update_adequate_forward
          | eapply dan_aexp_update_adequate_backward];
    eassumption.
Defined.

Lemma dan_args_update_adequate_forward :
  forall (aexps aexps': list aexp_Dan) (x: ident) (a: aexp_Dan),
    aexps' = map (fun exp : aexp_Dan => dan_aexp_update x a exp) aexps ->
    dan_args_update_rel x a aexps aexps'.
Proof.
  induction aexps; intros; simpl in H; subst; econstructor.
  - eapply dan_aexp_update_adequacy. reflexivity.
  - eapply IHaexps. reflexivity.
Defined.

Theorem dan_args_update_adequacy :
  forall (x: ident) (a: aexp_Dan) (aexps aexps': list aexp_Dan),
    aexps' = map (fun exp : aexp_Dan => dan_aexp_update x a exp) aexps <->
      dan_args_update_rel x a aexps aexps'.
Proof.
  split;
    intros;
    first [ eapply dan_args_update_adequate_backward
          | eapply dan_args_update_adequate_forward];
    eauto.
Defined.

                              


Lemma dan_bexp_update_adequate_forward :
  forall (bexp bexp': bexp_Dan) (x: ident) (a: aexp_Dan),
    bexp' = dan_bexp_update x a bexp ->
    dan_bexp_update_rel x a bexp bexp'.
Proof.
  induction bexp; intros; simpl in H; subst; econstructor;
    first [ eapply IHbexp
          | eapply IHbexp1
          | eapply IHbexp2
          | eapply dan_aexp_update_adequacy];
    eauto.
Defined.


Lemma dan_bexp_update_adequate_backward :
  forall (bexp bexp': bexp_Dan) (x: ident) (a: aexp_Dan),
    dan_bexp_update_rel x a bexp bexp' ->
    bexp' = dan_bexp_update x a bexp.
Proof.
  induction bexp; intros; invs H; simpl; try eauto; f_equal;
    first [ eapply IHbexp
          | eapply IHbexp1
          | eapply IHbexp2
          | eapply dan_aexp_update_adequacy];
    eauto.
Defined.

Theorem dan_bexp_update_adequacy :
  forall (bexp bexp': bexp_Dan) (x: ident) (a: aexp_Dan),
    bexp' = dan_bexp_update x a bexp <->
      dan_bexp_update_rel x a bexp bexp'.
Proof.
  split; intros;
    first [ eapply dan_bexp_update_adequate_forward
          | eapply dan_bexp_update_adequate_backward];
    eassumption.
Defined.

Lemma dan_lp_subst_adequate_forward :
  forall (d d': Dan_lp) (x: ident) (a: aexp_Dan),
    d' = subst_Dan_lp x a d ->
    subst_Dan_lp_rel x a d d'.
Proof.
  induction d'; intros.
  - destruct d; [ | simpl in H; invs H ].
    econstructor.
    simpl in H. inversion H.
    eapply transform_prop_exprs_adequacy_forward.
    eapply dan_aexp_update_adequacy.
    reflexivity.
  - destruct d; [simpl in H; invs H | ].
    econstructor. simpl in H. inversion H.
    eapply transform_prop_exprs_adequacy_forward.
    intros.
    eapply dan_bexp_update_adequacy.
    reflexivity.
Defined.



Lemma dan_log_subst_adequate_forward :
  forall (d d': AbsEnv) (x: ident) (a: aexp_Dan),
    d' = subst_AbsEnv x a d ->
    subst_AbsEnv_rel x a d d'.
Proof.
  induction d; intros; simpl in H; rewrite H.
  - econstructor.
    eapply dan_lp_subst_adequate_forward.
    reflexivity.
  - econstructor; first [ eapply IHd1 | eapply IHd2 ]; eauto.
  - econstructor; first [ eapply IHd1 | eapply IHd2 ]; eauto.
Defined.


Lemma dan_lp_subst_adequate_backward :
  forall (d d': Dan_lp) (x: ident) (a: aexp_Dan),
    subst_Dan_lp_rel x a d d' ->
    d' = subst_Dan_lp x a d.
Proof.
  induction d; intros; invs H; simpl.
  - eapply transform_prop_exprs_adequacy_backward in H3.
    + f_equal. rewrite H3. eauto.
    + intros; split; intros; eapply dan_aexp_update_adequacy; eauto.
  - eapply transform_prop_exprs_adequacy_backward in H3.
    + f_equal. rewrite H3. eauto.
    + intros; split; intros; eapply dan_bexp_update_adequacy; eauto.
Defined.

Lemma dan_log_subst_adequate_backward :
  forall (d d': AbsEnv) (x: ident) (a: aexp_Dan),
    subst_AbsEnv_rel x a d d' ->
    d' = subst_AbsEnv x a d.
Proof.
  induction d; intros; invs H; simpl.
  - eapply dan_lp_subst_adequate_backward in H3. subst. eauto.
  - eapply IHd1 in H4. eapply IHd2 in H6. subst. eauto.
  - eapply IHd1 in H4. eapply IHd2 in H6. subst. eauto. 
Defined.

Theorem dan_lp_subst_adequacy :
  forall (d d': Dan_lp) (x: ident) (a: aexp_Dan),
    d' = subst_Dan_lp x a d <->
      subst_Dan_lp_rel x a d d'.
Proof.
  split; intros;
    first [ eapply dan_lp_subst_adequate_forward
          | eapply dan_lp_subst_adequate_backward ];
    eauto.
Defined.

Theorem dan_log_subst_adequacy :
  forall (d d': AbsEnv) (x: ident) (a: aexp_Dan),
    d' = subst_AbsEnv x a d <->
      subst_AbsEnv_rel x a d d'.
Proof.
  split; intros;
    first [ eapply dan_log_subst_adequate_forward
          | eapply dan_log_subst_adequate_backward ];
    eauto.
Defined.
                      
