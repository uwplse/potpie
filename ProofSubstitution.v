From Coq Require Import String List Peano Arith Program.Equality.
From DanTrick Require Import DanLogHoare.
From DanTrick Require Import DanTrickLanguage.
From DanTrick Require Import EnvToStack.
From DanTrick Require Import StackLanguage.
From DanTrick Require Import DanLogProp.
From DanTrick Require Import LogicProp.
From DanTrick Require Import StackLangTheorems.
From DanTrick Require Import StackLogicBase.
From DanTrick Require Import LogicTranslationBase.
From DanTrick Require Import ImpVarMapTheorems.
From DanTrick Require Import CompilerCorrectHelpers.

Local Open Scope dantrick_scope.

(** Theorems about how substitution interacts with compilation
 * in both expressions and assertions *)


Lemma arith_compiled_substitution :
  forall (a : aexp_Dan) (idents : list DanTrickLanguage.ident) (n_args : nat) (ARG : aexp_stack)
    (WF: var_map_wf_wrt_aexp idents a)
    (HeqARG : ARG = comp_arith idents a)
    (x0 : string)
    (IN_MAP: In x0 idents)
    (aexp a0 : aexp_Dan)
    (ARG0 : aexp_stack)
    (HeqARG0 : ARG0 = comp_arith idents
                                 a0)
    (UPDATE : dan_aexp_update_rel x0 aexp a0 a)
    (ARG1 : aexp_stack)
    (HeqARG1 : ARG1 = compile_aexp aexp (ident_list_to_map idents) (Datatypes.length idents))
    (ARG2 : nat)
    (HeqARG2 : ARG2 = ident_list_to_map idents x0),
    arith_update_rel ARG2 ARG1 ARG0 ARG.
Proof.
  eapply (aexp_Dan_ind2
            (fun (a: aexp_Dan) =>
               forall (idents : list DanTrickLanguage.ident) (n_args : nat) (ARG : aexp_stack)
    (WF: var_map_wf_wrt_aexp idents a)
    (HeqARG : ARG = comp_arith idents a)
    (x0 : string)
    (IN_MAP: In x0 idents)
    (aexp a0 : aexp_Dan)
    (ARG0 : aexp_stack)
    (HeqARG0 : ARG0 = comp_arith idents
                                 a0)
    (UPDATE : dan_aexp_update_rel x0 aexp a0 a)
    (ARG1 : aexp_stack)
    (HeqARG1 : ARG1 = compile_aexp aexp (ident_list_to_map idents) (Datatypes.length idents))
    (ARG2 : nat)
    (HeqARG2 : ARG2 = ident_list_to_map idents x0),
                 arith_update_rel ARG2 ARG1 ARG0 ARG)); unfold comp_arith; unfold ident_list_to_map; simpl; intros; [invs UPDATE .. | | | ]; simpl.
  - econstructor.
  - econstructor. reflexivity.
  - econstructor. econstructor.
  - econstructor. unfold not; intros.
    unfold var_map_wf_wrt_aexp, var_map_wf in WF.
    destruct WF as (WF & WF2).
    destruct WF as (A & B & C & D).
    destruct WF2 as (E & F & G & I).

    remember (one_index_opt x0 idents) as n__x0.
      remember (one_index_opt x idents) as n__x.
      destruct n__x0, n__x.
      * unfold one_index_opt in Heqn__x0.
        destruct idents.
        -- discriminate.
        -- destruct (string_dec i x0); try discriminate.
      * invs H.
      * invs H.
      * symmetry in Heqn__x0. symmetry in Heqn__x.
        destruct idents.
        -- specialize (E x (free_vars_aexp_src (VAR_Dan x))).
           remember (free_vars_aexp_src (VAR_Dan x)) as free_aexp_vars.
           assert (free_aexp_vars = free_aexp_vars) by reflexivity.
           rewrite Heqfree_aexp_vars in *. eapply E in H0.
           invs H0.
           simpl. left. reflexivity.
        -- pose proof (Hx := Heqn__x).
           specialize (G x (free_vars_aexp_src (VAR_Dan x))).
           assert (free_vars_aexp_src (VAR_Dan x) = free_vars_aexp_src (VAR_Dan x)) by reflexivity.
           apply G in H0.
           destruct H0.
           pose proof (Hx' := H0).
           eapply find_index_rel_within_range in H0.
           
           eapply B in Heqn__x. eapply B in Heqn__x0.
           eapply find_index_rel_deterministic in Heqn__x0.
           symmetry in Heqn__x0. eapply H3 in Heqn__x0.
           assumption.
           invs H.
           assumption.
           eapply find_index_rel_within_range.
           pose proof (Heqn__x' := Heqn__x).
           eapply find_index_rel_deterministic in Heqn__x.
           invs H.
           eassumption.
           eassumption.
           pose proof (Hx'' := Hx').
           eapply find_index_rel_implication in Hx''.
           rewrite Hx'' in Hx. invs Hx.
           eapply find_index_rel_within_range.
           eassumption.
           simpl. left. reflexivity.
  - subst. invs UPDATE.
    unfold comp_arith in *.
    simpl. econstructor.
    unfold ident_list_to_map.
    unfold var_map_wf_wrt_aexp, var_map_wf in WF.
    destruct WF as (WF & WF_AEXP).
    destruct WF_AEXP as (AEXP_SUBSET & AEXP_HAS & AEXP_FIND & AEXP_ARGS).
    destruct WF as (NODUP & RANGE & IN & HAS).
    unfold not. intros.
    pose proof (IN_MAP' := IN_MAP).
    eapply IN in IN_MAP.
    destruct IN_MAP.
    eapply inside_implies_within_range in IN_MAP'; [ | eapply H0].
    assert (S x <= Datatypes.length idents) by intuition.
    rewrite <- H0 in H1.
    assert (one_index_opt x0 idents < S (Datatypes.length idents)).
    
    
    intuition.
    rewrite Nat.add_1_r in H.
    eapply bad_comparison in H.
    assumption.

    eapply bad_comparison in H.
    inversion H.

    assumption.
  - econstructor. reflexivity.
  - inversion UPDATE; unfold comp_arith; simpl.
    pose proof (AEXP := compile_aexp_args_adequate_backwards).
    rewrite HeqARG0.
    rewrite HeqARG1.
    rewrite HeqARG.
    subst.
    econstructor.
    reflexivity.
    subst.
    econstructor.
    + fold compile_aexp. eapply H. eapply n_args.
      * solve_var_map_wf.
      * unfold comp_arith. ereflexivity.
      * eassumption.
      * ereflexivity.
      * eassumption.
      * reflexivity.
      * reflexivity.
    + eapply H0.
      * eapply n_args.
      * solve_var_map_wf.
      * reflexivity.
      * eassumption.
      * fold compile_aexp. ereflexivity.
      * eassumption.
      * ereflexivity.
      * reflexivity.
  - invs UPDATE; unfold comp_arith; simpl.
    econstructor. reflexivity. econstructor.
    + fold compile_aexp. eapply H. eapply n_args.
      * solve_var_map_wf.
      * unfold comp_arith. ereflexivity.
      * eassumption.
      * ereflexivity.
      * eassumption.
      * reflexivity.
      * reflexivity.
    + eapply H0.
      * eapply n_args.
      * solve_var_map_wf. 
      * reflexivity.
      * eassumption.
      * fold compile_aexp. ereflexivity.
      * eassumption.
      * ereflexivity.
      * reflexivity.
  - invs UPDATE.
    + simpl. econstructor. reflexivity.
    + simpl. econstructor.
      revert H4 UPDATE.
      revert args.
      induction aexps; intros; (invs H4; simpl; econstructor).
      * invs H.
        eapply H2.
        -- eapply n_args.
        -- solve_var_map_wf.
        -- reflexivity.
        -- eassumption.
        -- ereflexivity.
        -- eassumption.
        -- reflexivity.
        -- reflexivity.
      * eapply IHaexps.
        -- invs H. assumption.
        -- solve_var_map_wf.
        -- assumption.
        -- econstructor. assumption.
Qed.

Lemma lp_arith_transrelation_args_substitution :
  forall (a_list : list aexp_Dan)
    (idents : list DanTrickLanguage.ident)
    (n_args : nat)
    (blist : list aexp_stack)
    (x0 : string)
    (aexp : aexp_Dan)
    (a_list0 : list aexp_Dan)
    (IN : In x0 idents)
    (blist0 : list aexp_stack)
    (COMP1 : compile_prop_args_rel (comp_arith idents) a_list blist)
    (UPDATE : transformed_prop_exprs_args (V := nat)
            (fun aexp0 aexp' : aexp_Dan =>
               dan_aexp_update_rel x0 aexp aexp0 aexp') a_list0 a_list)
    (COMP2 : compile_prop_args_rel (comp_arith idents) a_list0 blist0)
    (WF : prop_args_rel (V:= nat) (var_map_wf_wrt_aexp idents) a_list),
    transformed_prop_exprs_args
      (V:= nat)
      (arith_update_rel
         (ident_list_to_map idents x0)
         (compile_aexp
            aexp (ident_list_to_map idents)
            (Datatypes.length idents))) blist0 blist.
Proof.
  induction a_list; intros.
  - invs UPDATE.
    invs COMP1. invs COMP2.
    econstructor.
  - invs COMP1. invs UPDATE. invs COMP2. invs WF. econstructor.
    + eapply arith_compiled_substitution; try eassumption; try ereflexivity.
    + eapply IHa_list; try eassumption.
Qed.

  


Lemma lp_arith_transrelation_substitution :
  forall (d : LogicProp nat aexp_Dan) (s : LogicProp nat aexp_stack) (idents : list DanTrickLanguage.ident) (args : nat),
    lp_arith_transrelation args idents d s ->
    forall (x0 : string) (a : aexp_Dan) (l : LogicProp nat aexp_Dan),
      DanLogSubst.subst_Dan_lp_rel x0 a (Dan_lp_arith l) (Dan_lp_arith d) ->
      In x0 idents ->
      forall (s1: LogicProp nat aexp_stack),
        transformed_prop_exprs (fun aexp aexp' : aexp_Dan => dan_aexp_update_rel x0 a aexp aexp') l d ->
        lp_arith_transrelation args idents l s1 ->
        prop_rel (V := nat) (var_map_wf_wrt_aexp idents) d ->
        transformed_prop_exprs
          (arith_update_rel (ident_list_to_map idents x0)
                            (compile_aexp a (ident_list_to_map idents) (Datatypes.length idents)))
          s1
          s.
Proof.
  induction d; intros s idents n_args LT1 x0 aexp d' SUB IN s' UPDATE LT2 WF; invs LT1.
  - invs H. invs UPDATE.
    invs LT2.
    invs H0. econstructor.
  - invs H. invs UPDATE. invs LT2. invs H0. econstructor.
  - invs H. invs UPDATE. invs LT2. invs H0. econstructor.
    
    unfold comp_arith in *.
    remember_all_in H0.
    remember_all_in HeqARG.
    remember_all_in HeqArg2.
    eapply arith_compiled_substitution.
    + eapply n_args.
    + rewrite HeqARG5 in WF. inversion WF. eassumption.
    + unfold comp_arith. reflexivity.
    + rewrite HeqARG5 in WF. inversion WF. unfold var_map_wf_wrt_aexp, var_map_wf in H4.
      destruct H4 as (WF' & WF'').
      eassumption.
    + unfold comp_arith. ereflexivity.
    + eassumption.
    + reflexivity.
    + reflexivity.
  - invs H. invs UPDATE. invs LT2. invs H0.
    econstructor.
    + invs SUB. invs H7. eapply arith_compiled_substitution.
      * try eassumption.
      * invs WF. eapply H8.
      * reflexivity.
      * eassumption.
      * ereflexivity.
      * eassumption.
      * reflexivity.
      * reflexivity.
    + invs SUB. invs H7.
      eapply arith_compiled_substitution;
        [ eassumption | invs WF;
                        match goal with
                        | [ H: var_map_wf_wrt_aexp _ a2 |- _ ] =>
                            eapply H
                        end
        | .. ]; try ereflexivity; try eassumption.
  - invs H. invs UPDATE. invs LT2. invs H0. invs WF.
    econstructor.
    + eapply IHd1.
      * econstructor. eassumption.
      * econstructor. eassumption.
      * assumption.
      * assumption.
      * econstructor. eassumption.
      * eassumption.
    + eapply IHd2; solve [ econstructor; eassumption | assumption | eassumption ].
  - invs H. invs UPDATE. invs LT2. invs H0. invs WF.
    econstructor; [eapply IHd1 | eapply IHd2 ]; solve [econstructor; eassumption | eassumption ].
  - invs H. invs UPDATE. invs LT2. invs H0. invs WF.
    econstructor;
    match goal with
    | [ |- _ (comp_arith idents ?a)  ] =>
        idtac;
        (eapply arith_compiled_substitution;
         [ eassumption
         | match goal with
           | [ H: var_map_wf_wrt_aexp idents a |- _ ] =>
               eapply H
           end
         | .. ])
    end; try ereflexivity; try eassumption.
  - invs H. invs UPDATE. invs LT2. invs H0. invs WF.
    econstructor.
    eapply lp_arith_transrelation_args_substitution; eassumption.
    Unshelve.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
Qed.










Lemma bool_compiled_substitution :
  forall (a : bexp_Dan)
    (idents : list DanTrickLanguage.ident)
    (args : nat)
    (x0 : string)
    (aexp : aexp_Dan)
    (a0 : bexp_Dan)
    (IN : In x0 idents)
    (UPDATE : dan_bexp_update_rel x0 aexp a0 a)
    (WF : var_map_wf_wrt_bexp idents a),
    bool_update_rel
      (ident_list_to_map idents x0)
      (compile_aexp
         aexp
         (ident_list_to_map idents)
         (Datatypes.length idents))
      (comp_bool idents a0)
      (comp_bool idents a).
Proof.
  induction a; intros; invs UPDATE; invs WF.
  - econstructor.
  - econstructor.
  - unfold comp_bool. simpl. econstructor.
    eapply IHa; try eassumption.
    unfold_wf_bexp; unfold_wf_bexp_in WF.
    + eapply WF0.
    + intros.
      eapply A.
      ereflexivity.
      simpl.
      rewrite H1 in H2. assumption.
    + intros.
      eapply bool_wf_help; try eassumption.
    + intros.
      eapply C. ereflexivity.
      simpl. rewrite H1 in H2. eassumption.
  - unfold comp_bool. simpl. econstructor.
    + eapply IHa1; try eassumption.
      unfold_wf_bexp; unfold_wf_bexp_in WF.
      * eapply WF0.
      * intros. eapply A. ereflexivity. simpl. rewrite H1 in H2.
        eapply ListSet.set_union_iff. left. assumption.
      * intros. eapply bool_wf_help; try eassumption.
      * intros. eapply C. ereflexivity.
        simpl. eapply ListSet.set_union_iff. left. rewrite H1 in H2.
        assumption.
    + eapply IHa2; try eassumption.
      unfold_wf_bexp; unfold_wf_bexp_in WF.
      * eapply WF0.
      * intros. eapply A. ereflexivity. simpl. rewrite H1 in H2.
        eapply ListSet.set_union_iff. right. assumption.
      * intros. eapply bool_wf_help; try eassumption.
      * intros. eapply C. ereflexivity.
        simpl. eapply ListSet.set_union_iff. right. rewrite H1 in H2.
        assumption.
  - unfold comp_bool. simpl. econstructor; [eapply IHa1 | eapply IHa2]; try eassumption; solve_var_map_wf.
  - unfold comp_bool. simpl. econstructor.
    + eapply arith_compiled_substitution with (a := a1).
      * eassumption.
      *
        solve_var_map_wf.
      * unfold comp_arith. ereflexivity.
      * eassumption.
      * unfold comp_arith; ereflexivity.
      * eassumption.
      * reflexivity.
      * reflexivity.
    + eapply arith_compiled_substitution with (a := a2).
      * eassumption.
      * solve_var_map_wf.
      * unfold comp_arith; ereflexivity.
      * eassumption.
      * unfold comp_arith; ereflexivity.
      * eassumption.
      * reflexivity.
      * reflexivity.
Qed.
        
Lemma lp_bool_transrelation_args_substitution :
  forall (a_list : list bexp_Dan)
    (idents : list DanTrickLanguage.ident)
    (n_args : nat)
    (blist : list bexp_stack)
    (x0 : string)
    (aexp : aexp_Dan)
    (a_list0 : list bexp_Dan)
    (IN : In x0 idents)
    (blist0 : list bexp_stack)
    (COMP1 : compile_prop_args_rel (comp_bool idents) a_list blist)
    (UPDATE : transformed_prop_exprs_args
                (V := bool)
                (fun bexp0 bexp' : bexp_Dan =>
                   dan_bexp_update_rel x0 aexp bexp0 bexp')
                a_list0
                a_list)
    (COMP2 : compile_prop_args_rel
               (comp_bool idents)
               a_list0
               blist0)
    (WF : prop_args_rel (V:= bool) (var_map_wf_wrt_bexp idents) a_list),
    transformed_prop_exprs_args
      (V:= bool)
      (bool_update_rel
         (ident_list_to_map idents x0)
         (compile_aexp
            aexp (ident_list_to_map idents)
            (Datatypes.length idents))) blist0 blist.
Proof.
  induction a_list; intros.
  - invs UPDATE.
    invs COMP1. invs COMP2.
    econstructor.
  - invs COMP1. invs UPDATE. invs COMP2. invs WF. econstructor.
    + eapply bool_compiled_substitution; try eassumption; try ereflexivity.
    + eapply IHa_list; eassumption.
Qed.


Lemma lp_bool_transrelation_substitution :
  forall (d : LogicProp bool bexp_Dan) (s : LogicProp bool bexp_stack) (idents : list DanTrickLanguage.ident) (args : nat),
    lp_bool_transrelation args idents d s ->
    forall (x0 : string) (a : aexp_Dan) (l : LogicProp bool bexp_Dan),
      DanLogSubst.subst_Dan_lp_rel x0 a (Dan_lp_bool l) (Dan_lp_bool d) ->
      In x0 idents ->
      forall (s1: LogicProp bool bexp_stack),
        transformed_prop_exprs (fun bexp bexp' : bexp_Dan => dan_bexp_update_rel x0 a bexp bexp') l d ->
        lp_bool_transrelation args idents l s1 ->
        prop_rel (V := bool) (var_map_wf_wrt_bexp idents) d ->
        transformed_prop_exprs
          (bool_update_rel (ident_list_to_map idents x0)
                            (compile_aexp a (ident_list_to_map idents) (Datatypes.length idents)))
          s1
          s.
Proof.
  induction d; intros s idents args LT1; intros x0 aexp d';
    intros SUB IN; intros s';
    intros UPDATE LT2 WF; invs LT1; invs H; invs UPDATE; invs LT2; invs H0; invs WF.
  - econstructor.
  - econstructor.
  - econstructor.
    eapply bool_compiled_substitution; eassumption.
  - econstructor; eapply bool_compiled_substitution; eassumption.
  - econstructor; [eapply IHd1 | eapply IHd2]; solve [econstructor; eassumption | eassumption ].
  - econstructor; [eapply IHd1 | eapply IHd2]; solve [econstructor; eassumption | eassumption ].
  - econstructor; eapply bool_compiled_substitution; eassumption.
  - econstructor; eapply lp_bool_transrelation_args_substitution; try eassumption.
    Unshelve.
    all: eassumption.
Qed.
  

Lemma lp_transrelation_substitution' :
  forall (k args : nat) (idents : list DanTrickLanguage.ident) (d0 : Dan_lp) (s' : MetavarPred),
    lp_transrelation args idents d0 s' ->
    forall (d : Dan_lp) (x0 : string) (a : aexp_Dan),
      DanLogSubst.subst_Dan_lp_rel x0 a d d0 ->
      In x0 idents ->
      forall (mapping : ident -> nat) (a_stk : aexp_stack) (s : MetavarPred),
        lp_transrelation args idents d s ->
        Dan_lp_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d0 ->
        mapping = ident_list_to_map idents ->
        a_stk = compile_aexp a mapping (Datatypes.length idents) ->
        k = mapping x0 ->
        meta_update_rel k a_stk s s'.
Proof.
  intros ? ? ? ? ?.
  intros LT. dependent induction LT; intros ? ? ?; intros SUB IN; intros ? ? ?; intros LT' WF MAP COMP XMAP.
  - invs SUB.
    invs LT'. econstructor.
    eapply lp_arith_transrelation_substitution; try eassumption.
    invs WF.
    assumption.
  - invs SUB. invs LT'.  econstructor.
    eapply lp_bool_transrelation_substitution; try eassumption.
    invs WF.
    eassumption.
Qed.





Lemma well_formed_preserved_by_compilation :
  forall (a: aexp_Dan) (idents: list DanTrickLanguage.ident),
    var_map_wf_wrt_aexp idents a ->
    StackExprWellFormed.aexp_well_formed
      (compile_aexp a (ident_list_to_map idents) (Datatypes.length idents)).
Proof.
  eapply (aexp_Dan_ind2
            (fun a =>
               forall (idents: list DanTrickLanguage.ident),
    var_map_wf_wrt_aexp idents a ->
    StackExprWellFormed.aexp_well_formed
      (compile_aexp a (ident_list_to_map idents) (Datatypes.length idents)))); intros.
  - econstructor.
  - unfold_wf_aexp_in H.
    econstructor. unfold ident_list_to_map.
    unfold one_index_opt.
    destruct idents.
    auto.
    destruct (string_dec i x).
    auto. intuition.
  - simpl. econstructor. intuition.
  - simpl. econstructor.
    eapply H. eapply var_map_wf_plus_minus_dan_left. left. ereflexivity.
    eassumption.
    eapply H0.
    eapply var_map_wf_plus_minus_dan_right. left. ereflexivity. eassumption.
  - simpl. econstructor.
    eapply H. eapply var_map_wf_plus_minus_dan_left. right. ereflexivity.
    eassumption.
    eapply H0.
    eapply var_map_wf_plus_minus_dan_right. right. ereflexivity. eassumption.
  - simpl. econstructor. induction H.
    + simpl. econstructor.
    + simpl. econstructor.
      * eapply H.
        eapply var_map_wf_app_dan_args_first.
        eassumption.
      * eapply IHForall.
        eapply var_map_wf_app_dan_args_rest.
        eassumption.
Qed.

Lemma bool_well_formed_preserved_by_compilation :
  forall (b: bexp_Dan) (idents: list DanTrickLanguage.ident),
    var_map_wf_wrt_bexp idents b ->
    StackExprWellFormed.bexp_well_formed
      (compile_bexp b (ident_list_to_map idents) (Datatypes.length idents)).
Proof.
  induction b; intros idents WF; refold compile_bexp.
  - econstructor.
  - econstructor.
  - econstructor. eapply IHb.
    eapply var_map_wf_neg_dan; try ereflexivity; try eassumption.
  - econstructor; [eapply IHb1 | eapply IHb2]; [ eapply var_map_wf_and_or_dan_left | eapply var_map_wf_and_or_dan_right ]; try (left; ereflexivity); eassumption.
  - econstructor; [eapply IHb1 | eapply IHb2]; [ eapply var_map_wf_and_or_dan_left | eapply var_map_wf_and_or_dan_right ]; try (right; ereflexivity); eassumption.
  - econstructor; eapply well_formed_preserved_by_compilation; [ eapply var_map_wf_leq_dan_left | eapply var_map_wf_leq_dan_right]; try ereflexivity; eassumption.
Qed.

Lemma well_formed_arith_lp_args :
  forall (l: list aexp_Dan) (s0: list aexp_stack) 
    (idents: list ident)
    (n_loc_vars: nat),
    prop_args_rel (V := nat) (var_map_wf_wrt_aexp idents) l ->
    compile_prop_args_rel (comp_arith idents) l s0 ->
    prop_args_rel (V := nat) StackExprWellFormed.aexp_well_formed s0.
Proof.
  induction l; intros s0 idents n_loc_vars PROP COMP.
  - invs COMP. econstructor.
  - invs PROP. invs COMP. econstructor.
    + eapply well_formed_preserved_by_compilation.
      eassumption.
    + eapply IHl; try eassumption.
Qed.

Lemma well_formed_arith_lp :
  forall (l: LogicProp nat aexp_Dan) (s0: LogicProp nat aexp_stack) 
    (idents: list ident)
    (n_loc_vars: nat),
    prop_rel (var_map_wf_wrt_aexp idents) l ->
    lp_arith_transrelation n_loc_vars idents l s0 ->
    prop_rel StackExprWellFormed.aexp_well_formed s0.
Proof.
  induction l; intros s0 idents n_loc_vars WF LP; invs LP;
    match goal with
    | [ H: compile_prop_rel _ _ _ |- _ ] =>
        invs H
    end;
    invs WF;
    econstructor.
  - unfold comp_arith in *.
    eapply well_formed_preserved_by_compilation.
    eassumption.
  - unfold comp_arith in *.
    eapply well_formed_preserved_by_compilation.
    eassumption.
  - eapply well_formed_preserved_by_compilation.
    eassumption.
  - eapply IHl1; solve [eassumption | econstructor; eassumption ].
  - eapply IHl2; solve [eassumption | econstructor; eassumption ].
  - eapply IHl1; solve [eassumption | econstructor; eassumption ].
  - eapply IHl2; solve [eassumption | econstructor; eassumption ].
  - eapply well_formed_preserved_by_compilation.
    eassumption.
  - eapply well_formed_preserved_by_compilation.
    eassumption.
  - eapply well_formed_preserved_by_compilation.
    eassumption.
  - eapply well_formed_arith_lp_args; eassumption.
    Unshelve.
    all: eassumption.
Qed.

Lemma well_formed_bool_lp_args :
  forall (l: list bexp_Dan) (s0: list bexp_stack) 
    (idents: list ident)
    (n_loc_vars: nat),
    prop_args_rel (V := bool) (var_map_wf_wrt_bexp idents) l ->
    compile_prop_args_rel (comp_bool idents) l s0 ->
    prop_args_rel (V := bool) StackExprWellFormed.bexp_well_formed s0.
Proof.
  induction l; intros s0 idents n_loc_vars PROP COMP.
  - invs COMP. econstructor.
  - invs PROP. invs COMP. econstructor.
    + eapply bool_well_formed_preserved_by_compilation.
      eassumption.
    + eapply IHl; try eassumption.
Qed.

Lemma well_formed_bool_lp :
  forall (l: LogicProp bool bexp_Dan) (s0: LogicProp bool bexp_stack)
    (idents: list ident)
    (n_loc_vars: nat),
    prop_rel (var_map_wf_wrt_bexp idents) l ->
    lp_bool_transrelation n_loc_vars idents l s0 ->
    prop_rel StackExprWellFormed.bexp_well_formed s0.
Proof.
  induction l; intros s0 idents n_loc_vars WF LP; invs LP;
    match goal with
    | [ H: compile_prop_rel _ _ _ |- _ ] =>
        invs H
    end;
    invs WF;
    econstructor;
    try (eapply bool_well_formed_preserved_by_compilation; eassumption).
  - eapply IHl1; try eassumption. invs LP. econstructor. invs H0. eassumption.
  - eapply IHl2; try eassumption. invs LP. econstructor. invs H0. eassumption.
  - eapply IHl1; try eassumption. invs LP. econstructor. invs H0. eassumption.
  - eapply IHl2; try eassumption. invs LP. econstructor. invs H0. eassumption.
  - eapply well_formed_bool_lp_args.
    eassumption.
    eassumption.
    eassumption.
    Unshelve.
    all: eassumption.
Qed.



Lemma well_formed_preserved_by_aexp_update_backwards :
  forall (aexp aexp': aexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan)
    (WF_A: var_map_wf_wrt_aexp idents a)
    (IN: In x0 idents)
    (UPDATE: dan_aexp_update_rel x0 a aexp aexp')
    (WF: var_map_wf_wrt_aexp idents aexp),
    var_map_wf_wrt_aexp idents aexp'.
Proof.
  intros aexp aexp' idents x0 a WF_A IN UPDATE WF.
  revert WF. revert UPDATE. revert IN. revert WF_A. revert aexp' idents x0 a. revert aexp.
  apply (aexp_Dan_ind2
           (fun aexp =>
              forall (aexp': aexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan)
                (WF_A: var_map_wf_wrt_aexp idents a)
    (IN: In x0 idents)
    (UPDATE: dan_aexp_update_rel x0 a aexp aexp')
    (WF: var_map_wf_wrt_aexp idents aexp),
                var_map_wf_wrt_aexp idents aexp')); intros; invs UPDATE.
  - eassumption.
  - eassumption.
  - eassumption.
  - eassumption.
  - eapply var_map_wf_plus_dan_backwards;
      eapply var_map_wf_plus_dan_forwards in WF; destruct WF as (WF1 & WF2).
    + eapply H. eapply WF_A.
      eassumption.
      eassumption.
      eassumption.
    + eapply H0; [ eapply WF_A | eassumption .. ].
  - eapply var_map_wf_minus_dan_backwards;
      eapply var_map_wf_minus_dan_forwards in WF; destruct WF as (WF1 & WF2);
      (split; (idtac; solve [eapply H; [ eapply WF_A | eassumption .. ]
                            | eapply H0; [ eapply WF_A | eassumption .. ]])).
  - revert UPDATE. revert WF. revert H5.
    revert args'. induction H; intros.
    + invs UPDATE. invs H2.
      eassumption.
    + invs UPDATE. invs H4.
      eapply var_map_wf_app_dan_first_and_rest with (aexp := x) (aexps := l) (f := f) in WF.
      destruct WF.
      eapply var_map_wf_app_dan_first_and_rest_backward.
      assumption.
      split.
      * eapply H. eapply WF_A. eapply IN. eassumption. eassumption.
      * eapply IHForall.
        eassumption. eassumption. econstructor.
        assumption.
      * reflexivity.
Qed.



                        

Lemma well_formed_preserved_by_aexp_update :
  forall (aexp aexp': aexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan)
    (WF_A: var_map_wf_wrt_aexp idents a)
    (IN: In x0 idents)
    (UPDATE: dan_aexp_update_rel x0 a aexp aexp')
    (WF: var_map_wf_wrt_aexp idents aexp'),
    var_map_wf_wrt_aexp idents aexp.
Proof.
  intros aexp aexp' idents x0 a WF_A IN UPDATE WF.
  revert WF. revert UPDATE. revert IN. revert WF_A. revert aexp' idents x0 a. revert aexp.
  apply (aexp_Dan_ind2
           (fun aexp =>
              forall (aexp': aexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan)
                (WF_A: var_map_wf_wrt_aexp idents a)
    (IN: In x0 idents)
    (UPDATE: dan_aexp_update_rel x0 a aexp aexp')
    (WF: var_map_wf_wrt_aexp idents aexp'),
                var_map_wf_wrt_aexp idents aexp)); intros.
  - invs UPDATE. eassumption.
  - invs UPDATE.
    + unfold_wf_aexp_in WF.
      destruct WF0 as (NODUP & _).
      eapply var_map_wf_var_dan; eassumption.
    + assumption.
  - invs UPDATE.
    assumption.
  - invs UPDATE.
    eapply var_map_wf_plus_dan_backwards.
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
  - invs UPDATE. eapply var_map_wf_minus_dan_backwards; [eapply H | eapply H0]; solve [ eapply WF_A | eassumption | solve_var_map_wf].
  - invs UPDATE.
    revert H5.
    revert UPDATE.
    revert WF. revert args'.
    induction H; intros.
    + invs H5. eassumption.
    + invs H5. eapply var_map_wf_app_dan_backwards.
      * eapply H.
        eapply WF_A.
        eassumption.
        eassumption.
        eapply var_map_wf_app_dan_first.
        ereflexivity.
        eassumption.
      * eapply var_map_wf_app_dan_args_rest in WF.
        eapply IHForall.
        eassumption.
        econstructor.
        eassumption. assumption.
Qed.

Lemma var_map_wf_and_or_dan_backwards :
  forall (b1 b2 b3: bexp_Dan) (idents: list ident),
    (b3 = (AND_Dan b1 b2) \/ b3 = (OR_Dan b1 b2)) ->
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

Lemma var_map_wf_leq_dan_backwards :
  forall (b: bexp_Dan) (a1 a2: aexp_Dan) (idents: list ident),
    b = LEQ_Dan a1 a2 ->
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
  forall (bexp bexp': bexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan)
    (WF_A: var_map_wf_wrt_aexp idents a)
    (IN: In x0 idents)
    (UPDATE: dan_bexp_update_rel x0 a bexp bexp')
    (WF: var_map_wf_wrt_bexp idents bexp'),
    var_map_wf_wrt_bexp idents bexp.
Proof.
  induction bexp; intros.
  - invs UPDATE. assumption.
  - invs UPDATE. assumption.
  - invs UPDATE. eapply var_map_wf_neg_dan_forwards.
    reflexivity.
    eapply var_map_wf_neg_dan in WF; [ | reflexivity ].
    eapply IHbexp.
    eassumption. eassumption.
    eassumption. assumption.
  - invs UPDATE. eapply var_map_wf_and_or_dan_forwards in WF; [ | left; reflexivity ]. destruct WF as (WF1 & WF2). eapply var_map_wf_and_or_dan_backwards.
    left. reflexivity. split.
    + eapply IHbexp1; eassumption.
    + eapply IHbexp2; eassumption.
  - invs UPDATE. eapply var_map_wf_and_or_dan_forwards in WF; [ | right; reflexivity ]. destruct WF as (WF1 & WF2). eapply var_map_wf_and_or_dan_backwards.
    right. reflexivity. split.
    + eapply IHbexp1; eassumption.
    + eapply IHbexp2; eassumption.
  - invs UPDATE. eapply var_map_wf_leq_dan_forwards in WF; [ | reflexivity ].
    destruct WF as (WF1 & WF2).
    eapply var_map_wf_leq_dan_backwards. reflexivity.
    split.
    + eapply well_formed_preserved_by_aexp_update.
      * eapply WF_A.
      * eassumption.
      * eassumption.
      * eassumption.
    + eapply well_formed_preserved_by_aexp_update with (aexp := a2) (a := a); eassumption.
Qed.


Lemma well_formed_preserved_by_logic_prop_update_args :
  forall (a_list a_list': list aexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs_args (V := nat) (fun aexp aexp' : aexp_Dan => dan_aexp_update_rel x0 a aexp aexp') a_list a_list' ->
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
  forall (a_list a_list': list aexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs_args (V := nat) (fun aexp aexp' : aexp_Dan => dan_aexp_update_rel x0 a aexp aexp') a_list a_list' ->
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
  forall (lp lp': LogicProp nat aexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs (fun aexp aexp' : aexp_Dan => dan_aexp_update_rel x0 a aexp aexp') lp lp' ->
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
  forall (lp lp': LogicProp nat aexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs (fun aexp aexp' : aexp_Dan => dan_aexp_update_rel x0 a aexp aexp') lp lp' ->
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
  forall (b_list b_list': list bexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs_args (V := bool) (fun bexp bexp' : bexp_Dan => dan_bexp_update_rel x0 a bexp bexp') b_list b_list' ->
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
  forall (lp lp': LogicProp bool bexp_Dan) (idents: list ident) (x0: ident) (a: aexp_Dan),
    var_map_wf_wrt_aexp idents a ->
    In x0 idents ->
    transformed_prop_exprs (fun bexp bexp' : bexp_Dan => dan_bexp_update_rel x0 a bexp bexp') lp lp' ->
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


Lemma lp_transrelation_substitution :
  forall (k args : nat) (idents : list DanTrickLanguage.ident) (d0 : Dan_lp) (s : MetavarPred),
    lp_transrelation args idents d0 s ->
    forall (d : Dan_lp) (x0 : string) (a : aexp_Dan),
      DanLogSubst.subst_Dan_lp_rel x0 a d d0 ->
      In x0 idents ->
      forall (mapping : ident -> nat) (a_stk : aexp_stack) (s' : MetavarPred),
        lp_transrelation args idents d s' ->
        Dan_lp_prop_rel (var_map_wf_wrt_aexp idents)
                         (var_map_wf_wrt_bexp idents)
                         d0 ->
        var_map_wf_wrt_aexp idents a ->
        mapping = ident_list_to_map idents ->
        a_stk = compile_aexp a mapping (Datatypes.length idents) ->
        k = mapping x0 ->
        Dan_lp_prop_rel (var_map_wf_wrt_aexp idents)
                        (var_map_wf_wrt_bexp idents) d ->
        state_update_rel k a_stk (BaseState (AbsStkSize (Datatypes.length idents + args)) s') (BaseState (AbsStkSize (Datatypes.length idents + args)) s).
Proof.
  intros ? ? ? ? ?.
  intros LT. dependent induction LT; intros.
  + invs H0.
    invs H2.
    econstructor.
    * eapply lp_transrelation_substitution'.
      -- econstructor. eassumption.
      -- eassumption.
      -- eassumption.
      -- eassumption.
      -- eassumption.
      -- ereflexivity.
      -- reflexivity.
      -- reflexivity.
    * eapply well_formed_preserved_by_compilation.
      assumption.
    * econstructor. eapply well_formed_arith_lp.
      invs H8.
      eassumption.
      eassumption.
    * econstructor. unfold ident_list_to_map.
      unfold_wf_aexp_in H4.
      eapply inside_implies_within_range' in H1; [ | ereflexivity]. intuition.
  + invs H0. invs H2. invs H8.
    econstructor.
    * eapply lp_transrelation_substitution'; solve [econstructor; eassumption | eassumption | ereflexivity ].
    * eapply well_formed_preserved_by_compilation.
      assumption.
    * econstructor. eapply well_formed_bool_lp; eassumption.
    * econstructor. unfold ident_list_to_map.
      eapply inside_implies_within_range' in H1; [ | ereflexivity ].
      intuition.
Qed.

Lemma well_formed_preserved_by_log_prop_update :
  forall (d1 d: Dan_lp) (x: ident) (a: aexp_Dan) (idents: list ident),
    DanLogSubst.subst_AbsEnv_rel x a (AbsEnvLP d1) (AbsEnvLP d) ->
    In x idents ->
    var_map_wf_wrt_aexp idents a ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) (AbsEnvLP d) ->
    Dan_lp_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) d1.
Proof.
  induction d1; intros.
  - invs H2. invs H. invs H8.
    invs H6.
    econstructor. eapply well_formed_preserved_by_logic_prop_update; try eassumption.
  - invs H2. invs H. invs H8. invs H6.
    econstructor.
    eapply bool_well_formed_preserved_by_logic_prop_update; try eassumption.
Qed.

Lemma well_formed_preserved_by_dan_log_update :
  forall (l d: AbsEnv) (x: ident) (a: aexp_Dan) (idents: list ident),
    DanLogSubst.subst_AbsEnv_rel x a l d ->
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

Lemma metavarpred_well_formed_preserved_by_compilation :
  forall (l: Dan_lp) (s: MetavarPred) (args: nat) (idents: list ident),
     lp_transrelation args idents l s ->
     Dan_lp_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) l ->
     StackExprWellFormed.mv_well_formed s.
Proof.
  induction l; intros.
  - invs H. invs H0. econstructor. eapply well_formed_arith_lp; eassumption.
  - invs H. invs H0.  econstructor. eapply well_formed_bool_lp; eassumption.
Qed.

Lemma absstate_well_formed_preserved_by_compilation:
  forall (l: AbsEnv) (s: AbsState) (args: nat) (idents: list ident),
  logic_transrelation args idents l s ->
  AbsEnv_prop_rel (var_map_wf_wrt_aexp idents) (var_map_wf_wrt_bexp idents) l ->
  StackExprWellFormed.absstate_well_formed s.
Proof.
  induction l; intros.
  - invs H. invs H0. econstructor.
    eapply metavarpred_well_formed_preserved_by_compilation; eassumption.
  - invs H. invs H0. econstructor; [eapply IHl1 | eapply IHl2]; eassumption.
  - invs H. invs H0. econstructor; [eapply IHl1 | eapply IHl2]; eassumption.
Qed.


Lemma logic_transrelation_substitution :
  forall args ident_list d d0 s s' x a k a_stk mapping,
    logic_transrelation args ident_list d0 s ->
    DanLogSubst.subst_AbsEnv_rel x a d d0 ->
    In x ident_list ->
    var_map_wf_wrt_aexp ident_list a ->
    AbsEnv_prop_rel (var_map_wf_wrt_aexp ident_list)
                     (var_map_wf_wrt_bexp ident_list)
                     d0 ->
    mapping = ident_list_to_map ident_list ->
    a_stk = compile_aexp a mapping (List.length ident_list) ->
    logic_transrelation args ident_list d s' ->
    k = mapping x ->
    state_update_rel k a_stk s' s.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? LT.
  revert mapping a_stk s'.
  revert k x a d.
  dependent induction LT; intros.
  -  invs H6.
     + eapply lp_transrelation_substitution.
       * eassumption.
       * invs H0. eassumption.
       * eassumption.
       * eassumption.
       * invs H3. eassumption.
       * eassumption.
       * ereflexivity.
       * ereflexivity.
       * ereflexivity.
       * eapply well_formed_preserved_by_log_prop_update; eassumption.
     + invs H0.
     + invs H0.
  - invs H. invs H5. invs H2. econstructor.
    + eapply IHLT1; try eassumption; try ereflexivity.
    + eapply IHLT2; try eassumption; try ereflexivity.
    + eapply well_formed_preserved_by_compilation. assumption.
    + eapply well_formed_preserved_by_dan_log_update in H12; [ | eassumption .. ].
      eapply absstate_well_formed_preserved_by_compilation; eassumption.
    + eapply well_formed_preserved_by_dan_log_update in H13; [ | eassumption ..].
      eapply absstate_well_formed_preserved_by_compilation; eassumption.
  - invs H. invs H5. invs H2. econstructor.
    + eapply IHLT1; try eassumption; try ereflexivity.
    + eapply IHLT2; try eassumption; try ereflexivity.
    + eapply absstate_well_formed_preserved_by_compilation; try eassumption.
      eapply well_formed_preserved_by_dan_log_update in H9; try eassumption.
    + eapply well_formed_preserved_by_dan_log_update in H13; [ | eassumption ..].
      eapply absstate_well_formed_preserved_by_compilation; eassumption.
    + eapply well_formed_preserved_by_compilation. eassumption.
Qed.
