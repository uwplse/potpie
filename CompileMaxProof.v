From Coq Require Import Psatz Arith List Program.Equality String.
From DanTrick Require Import ProofCompiler StackLangTheorems ImpVarMap DanImpHigherOrderRel ProofCompilerBase DanLogProp LogicProp ProofCompilerHelpers DanHoareWF DanLogHoare DanImpHigherOrderRelTheorems LogicTranslationBase LogicTranslationAdequate.
From DanTrick Require Import ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed.
From DanTrick Require Import TranslationPure DanTrickLanguage.
From DanTrick Require Import ProofCompiler.
Import Tests.


Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Open Scope dantrick_scope.




Local Definition maxSmallCompMap := "z" :: nil.
Local Definition maxSmallCompProg := (IF_Dan (gt_Dan (PARAM_Dan 0) (PARAM_Dan 1)) (ASSIGN_Dan "z" (PARAM_Dan 0)) (ASSIGN_Dan "z" (PARAM_Dan 1))).





Lemma max_fenv_well_formed :
  fenv_well_formed' ((init_fenv "id") :: nil) init_fenv.
Proof.
  unfold fenv_well_formed'.
  split.
  - constructor.
    + unfold not; intros. invs H.
    + constructor.
  - intros. unfold init_fenv in H. split; [ | split ].
    + simpl. unfold init_fenv. right. assumption.
    + unfold init_fenv. rewrite H. simpl. constructor.
      constructor.
    + rewrite H. simpl. constructor. eapply String.eqb_eq. reflexivity.
Qed.

Lemma max_funcs_okay_too :
  funcs_okay_too ((init_fenv "id") :: nil) (EnvToStack.compile_fenv init_fenv).
Proof.
  unfold funcs_okay_too. econstructor.
  - unfold EnvToStack.compile_function. unfold EnvToStack.pre_compile_function. unfold EnvToStack.compile_code. unfold construct_trans. unfold free_vars_imp_src.
    unfold init_fenv.
    simpl. split.
    + econstructor.
      * econstructor.
      * econstructor.
        -- unfold stack_mapping. simpl. reflexivity.
        -- unfold stack_mapping. simpl. constructor. constructor.
        -- econstructor; constructor; constructor.
    + unfold EnvToStack.compile_fenv. unfold EnvToStack.compile_function. simpl.
      econstructor.
      * unfold stack_mapping. simpl. constructor.
      * unfold stack_mapping. simpl. constructor. constructor.
  - econstructor.
Qed.

Lemma max_funcs_params_ok :
  Forall (fun func => all_params_ok (DanTrickLanguage.Args func) (DanTrickLanguage.Body func)) ((init_fenv "id") :: nil).
Proof.
  constructor.
  - constructor. constructor. simpl. constructor.
  - constructor.
Qed.
  

Lemma max_fun_app_imp :
  fun_app_imp_well_formed init_fenv ((init_fenv "id") :: nil) maxSmallCompProg.
Proof.
  constructor; constructor; constructor; constructor; constructor; constructor.
Qed.




Lemma well_formed_assign_param0 :
  imp_rec_rel (var_map_wf_wrt_imp ("z" :: nil)) ("z" <- PARAM_Dan 0).
Proof.
  pose proof (H := "z" = "z").
  econstructor. unfold_wf_imp.
  * split; [ | split; [ | split ]]; intros.
    econstructor.
    unfold not; intros.
    invs H0.
    econstructor.
    eapply second_wf_proof; eassumption.
    invs H0.
    exists 0.
    simpl. reflexivity.
    invs H1.
    invs H0.
    revert H1. revert H0.
    induction imp; intros.
    unfold construct_trans in H1.
    simpl in H1. 
    eapply imp_has_variable_if_iff.
    rewrite H1 in H0.
    rewrite fold_left_is_reverse in H0.
    eapply in_preserved_by_reverse in H0.
    eapply ListSet.set_union_iff in H0. destruct H0.
    -- left.
       eapply free_vars_in_bexp_has_variable in H0; [ | ereflexivity ].
       eassumption.
    -- eapply ListSet.set_union_iff in H0.
       destruct H0.
       ++ right. left. eapply free_vars_in_imp_has_variable in H0.
          eassumption.
          reflexivity.
       ++ right. right. eapply free_vars_in_imp_has_variable in H0; [ | ereflexivity ]. eassumption.
    -- invs H1.
    -- eapply imp_has_variable_while_iff.
       unfold construct_trans in H1.
       rewrite H1 in H0.
       rewrite fold_left_is_reverse in H0.
       eapply in_preserved_by_reverse in H0.
       simpl in H0.
       eapply ListSet.set_union_iff in H0.
       destruct H0.
       ++ right. eapply free_vars_in_imp_has_variable in H0; [ | ereflexivity]; eassumption.
       ++ left. eapply free_vars_in_bexp_has_variable in H0; [ | ereflexivity ]; eassumption.
    -- eapply imp_has_variable_assign_iff.
       unfold construct_trans in H1. simpl in H1.
       rewrite H1 in H0.
       rewrite fold_left_is_reverse in H0.
       eapply in_preserved_by_reverse in H0.
       eapply ListSet.set_add_elim in H0.
       destruct H0.
       ++ left. subst. simpl. reflexivity.
       ++ unfold ListSet.set_In in H0.
          right. eapply free_vars_in_aexp_has_variable in H0; [ | ereflexivity ]; eassumption.
    -- unfold construct_trans in H1. simpl in H1. rewrite H1 in H0.
       rewrite fold_left_is_reverse in H0.
       eapply in_preserved_by_reverse in H0.
       eapply imp_has_variable_seq_iff.
       eapply ListSet.set_union_iff in H0. destruct H0; [ left | right ]; eapply free_vars_in_imp_has_variable in H0; try ereflexivity; eassumption.
    -- invs H2.
  * econstructor.
    unfold_wf_aexp; intros.
    -- split; [ | split; [ | split]]; intros.
       ++ econstructor. unfold not; intros. invs H0. econstructor.
       ++ eapply second_wf_proof; eassumption.
       ++ invs H0.
          ** exists 0. ereflexivity.
          ** invs H1.
       ++ unfold construct_trans in H1. rewrite fold_left_is_reverse in H1.
          rewrite H1 in H0. eapply in_preserved_by_reverse in H0.
          eapply free_vars_in_imp_has_variable in H0; [ | ereflexivity]; eassumption.
    -- simpl in H0. rewrite H0 in H1. invs H1.
    -- simpl in H0. rewrite H0 in H1. invs H1.
    -- simpl in H0. rewrite H0 in H1. invs H1.
    -- invs H0.
  * intros. eapply free_vars_in_imp_has_variable in H0; [ | ereflexivity ].
    simpl in H0. destruct H0; [ | invs H0].
    rewrite <- H0. econstructor. reflexivity.
Qed.







Lemma max_bexp_well_formed :
  var_map_wf_wrt_bexp ("z" :: nil) (PARAM_Dan 0 >d PARAM_Dan 1).
Proof.
  prove_var_map_wf_wrt_bexp_no_vars_in_bexp.
Qed.

Lemma well_formed_if_max :
  var_map_wf_wrt_imp ("z" :: nil)
                     (when (PARAM_Dan 0 >d PARAM_Dan 1) then "z" <- PARAM_Dan 0
                      else "z" <- PARAM_Dan 1 done).
Proof.
  unfold_wf_imp; intros.
  * split; [ | split; [ | split ]]; intros.
    -- prove_nodup_finite.
    -- eapply second_wf_proof; eassumption.
    -- eapply in_list_means_exists_index. eassumption.
    -- eapply free_vars_in_imp_alternate; eassumption.
  * econstructor.
    eapply max_bexp_well_formed.
    econstructor.
    prove_var_map_wf_wrt_aexp_no_vars_in_aexp.
    econstructor.
    prove_var_map_wf_wrt_aexp_no_vars_in_aexp.
  * eapply free_vars_in_imp_has_variable.
    assert ("z" :: nil = free_vars_imp_src (IF_Dan (PARAM_Dan 0 >d PARAM_Dan 1) (ASSIGN_Dan "z" (PARAM_Dan 0)) (ASSIGN_Dan "z" (PARAM_Dan 1)))).
    simpl. reflexivity.
    eassumption.
    eassumption.
Qed.

Lemma var_map_wf_bexp_z_geq_param0 :
  var_map_wf_wrt_bexp ("z" :: nil) (VAR_Dan "z" >=d PARAM_Dan 0).
Proof.
  unfold_wf_bexp; intros.
  - split; [ | split; [ | split ]]; intros; [prove_nodup_finite | eapply second_wf_proof; eassumption | eapply in_list_means_exists_index; eassumption | eapply free_vars_in_imp_alternate; eassumption ].
  - simpl in H.  rewrite H in H0. eassumption.
  - eapply free_vars_in_bexp_has_variable; eassumption.
  - simpl in H.  rewrite H in H0.
    invs H0.
    + exists 0. econstructor. reflexivity.
    + invs H1.
Qed.

Lemma var_map_wf_bexp_z_geq_param1 :
  var_map_wf_wrt_bexp ("z" :: nil) (VAR_Dan "z" >=d PARAM_Dan 1).
Proof.
  unfold_wf_bexp; intros.
  - split; [ | split; [ | split ]]; intros; [prove_nodup_finite | eapply second_wf_proof; eassumption | eapply in_list_means_exists_index; eassumption | eapply free_vars_in_imp_alternate; eassumption ].
  - simpl in H.  rewrite H in H0. eassumption.
  - eapply free_vars_in_bexp_has_variable; eassumption.
  - simpl in H.  rewrite H in H0.
    invs H0.
    + exists 0. econstructor. reflexivity.
    + invs H1.
Qed.

Lemma var_map_wf_bexp_param0_geq_param0 :
  var_map_wf_wrt_bexp ("z" :: nil) (PARAM_Dan 0 >=d PARAM_Dan 0).
Proof.
  prove_var_map_wf_wrt_bexp_no_vars_in_bexp.
Qed.

Lemma var_map_wf_bexp_param0_geq_param1 :
  var_map_wf_wrt_bexp ("z" :: nil) (PARAM_Dan 0 >=d PARAM_Dan 1).
Proof.
  prove_var_map_wf_wrt_bexp_no_vars_in_bexp.
Qed.

Lemma var_map_wf_bexp_param1_geq_param0 :
  var_map_wf_wrt_bexp ("z" :: nil) (PARAM_Dan 1 >=d PARAM_Dan 0).
Proof.
  prove_var_map_wf_wrt_bexp_no_vars_in_bexp.
Qed.

Lemma var_map_wf_bexp_param1_geq_param1 :
  var_map_wf_wrt_bexp ("z" :: nil) (PARAM_Dan 1 >=d PARAM_Dan 1).
Proof.
  prove_var_map_wf_wrt_bexp_no_vars_in_bexp.
Qed.

Lemma var_map_wf_bexp_param0_gt_param1 :
  var_map_wf_wrt_bexp ("z" :: nil) (PARAM_Dan 0 >d PARAM_Dan 1).
Proof.
  prove_var_map_wf_wrt_bexp_no_vars_in_bexp.
Qed.

Lemma wf_max_conclusion :
  AbsEnv_prop_wf ("z" :: nil)
                  (AbsEnvAnd
                     (AbsEnvLP
                        (Dan_lp_bool
                           (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                                      (VAR_Dan "z" >=d PARAM_Dan 0))))
                     (AbsEnvLP
                        (Dan_lp_bool
                           (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                                      (VAR_Dan "z" >=d PARAM_Dan 1))))).
Proof.
  constructor; constructor; constructor; constructor.
  apply var_map_wf_bexp_z_geq_param0.
  apply var_map_wf_bexp_z_geq_param1.
Qed.

Lemma wf_max_conclusion_map :
  CompilerAssumptionLogicTrans.log_Dan_wf_map ("z" :: nil)
                  (AbsEnvAnd
                     (AbsEnvLP
                        (Dan_lp_bool
                           (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                                      (VAR_Dan "z" >=d PARAM_Dan 0))))
                     (AbsEnvLP
                        (Dan_lp_bool
                           (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                                      (VAR_Dan "z" >=d PARAM_Dan 1))))).
Proof.
  constructor; constructor; constructor; constructor.
  apply var_map_wf_bexp_z_geq_param0.
  apply var_map_wf_bexp_z_geq_param1.
Qed.

Lemma wf_subst_param1_max_conclusion :
  AbsEnv_prop_wf ("z" :: nil)
                  (AbsEnvAnd
                     (AbsEnvLP
                        (Dan_lp_bool
                           (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                                      (PARAM_Dan 1 >=d PARAM_Dan 0))))
                     (AbsEnvLP
                        (Dan_lp_bool
                           (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                                      (PARAM_Dan 1 >=d PARAM_Dan 1))))).
Proof.
  constructor; constructor; constructor; constructor.
  eapply var_map_wf_bexp_param1_geq_param0.
  eapply var_map_wf_bexp_param1_geq_param1.
Qed.

Lemma maxSmallAimpAlwaysWf :
  aimp_always_wf ((init_fenv "id") :: nil) maxSmallCompMap 2 Source.dan_log_true maxSmallCompProg Source.max_conclusion init_fenv Source.maxSmallProof.
Proof.
  assert (Heq: (when (PARAM_Dan 0 >d PARAM_Dan 1) then "z" <- PARAM_Dan 0
                else "z" <- PARAM_Dan 1 done) = (when (PARAM_Dan 0 >d PARAM_Dan 1) then "z" <- PARAM_Dan 0
                                                else "z" <- PARAM_Dan 1 done)) by reflexivity.
  specialize (UIP_imp_refl _ Heq). intros.
  eapply HLDanWFIf with (heq := Heq).
  - rewrite H. simpl. unfold Source.maxSmallProof. f_equal.
  - constructor.
    + eapply well_formed_assign_param0.
    + eapply well_formed_assign_param1.
    + eapply well_formed_if_max.
  - constructor. constructor. constructor.
  - apply wf_max_conclusion.
  - eapply HLDanWFConsequence. ereflexivity.
    + apply well_formed_assign_param0.
    + unfold Source.param0geqparam0, Source.param0geqparam1.
      unfold Source.true_bool.
      constructor; constructor; constructor; constructor.
      eapply var_map_wf_bexp_param0_geq_param0.
      eapply var_map_wf_bexp_param0_geq_param1.
    + unfold atrueDan. constructor; constructor; constructor; constructor.
      eapply var_map_wf_bexp_param0_gt_param1.
    + unfold Source.max_conclusion. unfold Source.true_bool.
      apply wf_max_conclusion.
    + apply wf_max_conclusion.
    + unfold Source.max_conclusion. unfold Source.param0geqparam0. unfold Source.param0geqparam1. unfold Source.true_bool.
      assert (Heq' : (ASSIGN_Dan "z" (PARAM_Dan 0) = ASSIGN_Dan "z" (PARAM_Dan 0))) by reflexivity.
      specialize (UIP_imp_refl _ Heq'). intros.
      assert (DanLogSubst.subst_AbsEnv "z" (PARAM_Dan 0) (AbsEnvAnd
                                                             (AbsEnvLP
                                                                (Dan_lp_bool
                                                                   (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                                                                              (VAR_Dan "z" >=d PARAM_Dan 0))))
                                                             (AbsEnvLP
                                                                (Dan_lp_bool
                                                                   (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                                                                              (VAR_Dan "z" >=d PARAM_Dan 1))))) = (AbsEnvAnd
                                                                                                                    (AbsEnvLP
                                                                                                                       (Dan_lp_bool
                                                                                                                          (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                                                                                                                                     (PARAM_Dan 0 >=d PARAM_Dan 0))))
                                                                                                                    (AbsEnvLP
                                                                                                                       (Dan_lp_bool
                                                                                                                          (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                                                                                                                                     (PARAM_Dan 0 >=d PARAM_Dan 1)))))) by reflexivity.
      specialize (DanLogPropDec.UIP_AbsEnv_refl _ H1). intros.
      eapply HLDanWFAssign with (Heq := Heq') (Hsubst := H1).
      subst. simpl.
      f_equal.
      * apply wf_max_conclusion.
      * apply well_formed_assign_param0.
      * constructor. constructor. constructor. constructor. constructor. constructor. constructor. constructor. constructor. constructor. constructor. constructor. constructor.
      * apply wf_max_conclusion_map.
      * repeat constructor.
      * constructor. lia.
      * constructor.
    + constructor.
      * constructor. constructor. constructor. constructor; constructor.
      * constructor. constructor. constructor. constructor; constructor.
    + constructor; constructor; constructor; constructor; constructor; constructor; constructor; constructor; constructor.
    + constructor; constructor; constructor; constructor; constructor; constructor.
    + constructor; constructor; constructor; constructor; constructor; constructor.
    + constructor; constructor; constructor; constructor.
      -- eapply var_map_wf_bexp_param0_geq_param0.
      -- eapply var_map_wf_bexp_param0_geq_param1.
    + constructor; constructor; constructor; constructor. apply max_bexp_well_formed. 
    + apply wf_max_conclusion_map.
    + apply wf_max_conclusion_map.
    + repeat constructor.
    + repeat constructor.
    + repeat constructor.
    + repeat constructor.
  - eapply HLDanWFConsequence. simpl.
    f_equal.
    apply well_formed_assign_param1.
    apply wf_subst_param1_max_conclusion.
    econstructor; econstructor; econstructor; econstructor.
    eapply var_map_wf_bexp_param0_gt_param1.
    unfold Source.max_conclusion. unfold Source.true_bool.
    apply wf_max_conclusion.
    apply wf_max_conclusion. 
    pose (ASSIGN_Dan "z" (PARAM_Dan 1)) as IMP.
    assert (IMP = IMP) by reflexivity.
    specialize (UIP_imp_refl _ H0); intros.
    pose ((AbsEnvAnd
             (AbsEnvLP
                (Dan_lp_bool
                   (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                              (VAR_Dan "z" >=d PARAM_Dan 0))))
             (AbsEnvLP
                (Dan_lp_bool
                   (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                              (VAR_Dan "z" >=d PARAM_Dan 1)))))) as P.
    pose (AbsEnvAnd
            (AbsEnvLP
               (Dan_lp_bool
                  (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                             (PARAM_Dan 1 >=d PARAM_Dan 0))))
            (AbsEnvLP
               (Dan_lp_bool
                  (UnaryProp bool bexp_Dan (fun v : bool => v = true)
                             (PARAM_Dan 1 >=d PARAM_Dan 1))))) as P'.
    assert (DanLogSubst.subst_AbsEnv "z" (PARAM_Dan 1) P = P') by reflexivity.
    
    apply HLDanWFAssign with (Heq := H0) (Hsubst := H2).
    specialize (DanLogPropDec.UIP_AbsEnv_refl _ H2). intros.
    subst.
    simpl. unfold P. reflexivity.
    unfold P.
    apply wf_max_conclusion.
    unfold IMP.
    apply well_formed_assign_param1.
    all: try (constructor; constructor; constructor; constructor; constructor; constructor; constructor; constructor; constructor; auto with arith).
    + apply wf_max_conclusion_map.
    + constructor; constructor; constructor; constructor.
      * apply var_map_wf_bexp_param1_geq_param0.
      * apply var_map_wf_bexp_param1_geq_param1.
    + constructor; constructor; constructor; constructor.
      apply max_bexp_well_formed.
    + constructor; constructor; constructor; constructor.
      * apply var_map_wf_bexp_z_geq_param0.
      * apply var_map_wf_bexp_z_geq_param1.
    + apply wf_max_conclusion_map.
  - constructor; constructor; constructor.
  - constructor; constructor; constructor; constructor; constructor; constructor.
  - repeat constructor.
  - apply wf_max_conclusion_map.
  - repeat constructor.
  - repeat constructor.
Qed.


Lemma maxSmallVarMapWfWrtImp :
  imp_rec_rel (var_map_wf_wrt_imp maxSmallCompMap) maxSmallCompProg.
Proof.
  eapply imp_rec_rel_var_map_wf_adequacy_backward.
  unfold maxSmallCompMap. unfold maxSmallCompProg.
  exact well_formed_if_max.
Qed.

Lemma maxSmallDanLogPropRel1 :
  AbsEnv_prop_wf maxSmallCompMap Source.dan_log_true.
Proof.
  unfold AbsEnv_prop_wf, maxSmallCompMap, Source.dan_log_true.
  econstructor. econstructor. econstructor.
Qed.

Lemma maxSmallDanLogPropRel2 :
  AbsEnv_prop_wf maxSmallCompMap Source.max_conclusion.
Proof.
  unfold AbsEnv_prop_wf, maxSmallCompMap, Source.max_conclusion.
  unfold Source.true_bool.
  econstructor; econstructor; econstructor; econstructor.
  eapply var_map_wf_bexp_z_geq_param0.
  eapply var_map_wf_bexp_z_geq_param1.
Qed.


Lemma maxSmallTranslation1 :
  logic_transrelation 2 maxSmallCompMap Source.dan_log_true (comp_logic 2 maxSmallCompMap Source.dan_log_true).
Proof.
  eapply log_comp_adequacy.
  reflexivity.
Qed.

Lemma maxSmallTranslation2 :
  logic_transrelation 2 maxSmallCompMap Source.max_conclusion (comp_logic 2 maxSmallCompMap Source.max_conclusion).
Proof.
  eapply log_comp_adequacy; reflexivity.
Qed.

Lemma maxTerminatesHelper_z_geq_param0 :
  AbsEnv_prop_rel (CompilerAssumptionLogicTrans.aexp_terminates_always init_fenv 2)
    (CompilerAssumptionLogicTrans.bexp_terminates_always init_fenv 2)
    (AbsEnvLP (Dan_lp_bool (UnaryProp bool bexp_Dan (fun v : bool => v = true) (VAR_Dan "z" >=d PARAM_Dan 0)))).
Proof.
  constructor.
  repeat constructor.
  
  unfold CompilerAssumptionLogicTrans.bexp_terminates_always.
  intros.
  destruct dbenv. simpl in H. lia.
  destruct dbenv. simpl in H. lia.
  exists (Nat.leb n (nenv "z")).
  econstructor; econstructor.
  lia. reflexivity. reflexivity.
Qed.

Lemma maxTerminatesHelper_z_geq_param1 :
  AbsEnv_prop_rel (CompilerAssumptionLogicTrans.aexp_terminates_always init_fenv 2)
    (CompilerAssumptionLogicTrans.bexp_terminates_always init_fenv 2)
    (AbsEnvLP (Dan_lp_bool (UnaryProp bool bexp_Dan (fun v : bool => v = true) (VAR_Dan "z" >=d PARAM_Dan 1)))).
Proof.
  constructor.
  repeat constructor.
  
  unfold CompilerAssumptionLogicTrans.bexp_terminates_always.
  intros.
  destruct dbenv. simpl in H. lia.
  destruct dbenv. simpl in H. lia.
  exists (Nat.leb n0 (nenv "z")).
  econstructor; econstructor.
  lia. reflexivity. reflexivity.
Qed.

Lemma maxTerminatesHelper_max_conclusion :
  CompilerAssumptionLogicTrans.log_terminates_always init_fenv 2 Source.max_conclusion.
Proof.
  unfold Source.max_conclusion. unfold CompilerAssumptionLogicTrans.log_terminates_always.
  unfold Source.true_bool. econstructor.
  - eapply maxTerminatesHelper_z_geq_param0.
  - eapply maxTerminatesHelper_z_geq_param1.
Qed.

Lemma maxTerminatesHelper_param0_leq_param0 :
  AbsEnv_prop_rel (CompilerAssumptionLogicTrans.aexp_terminates_always init_fenv 2)
    (CompilerAssumptionLogicTrans.bexp_terminates_always init_fenv 2)
    (AbsEnvLP (Dan_lp_bool (UnaryProp bool bexp_Dan (fun v : bool => v = true) (PARAM_Dan 0 <=d PARAM_Dan 0)))).
Proof.
  constructor.
  repeat constructor.
  
  unfold CompilerAssumptionLogicTrans.bexp_terminates_always.
  intros.
  destruct dbenv. simpl in H. lia.
  destruct dbenv. simpl in H. lia.
  exists (Nat.leb n n).
  econstructor.
  econstructor. lia. simpl. reflexivity. econstructor. lia. reflexivity.
Qed.

Lemma maxTerminatesHelper_param1_leq_param0 :
  AbsEnv_prop_rel (CompilerAssumptionLogicTrans.aexp_terminates_always init_fenv 2)
    (CompilerAssumptionLogicTrans.bexp_terminates_always init_fenv 2)
    (AbsEnvLP (Dan_lp_bool (UnaryProp bool bexp_Dan (fun v : bool => v = true) (PARAM_Dan 1 <=d PARAM_Dan 0)))).
Proof.
  repeat constructor.
  unfold CompilerAssumptionLogicTrans.bexp_terminates_always.
  intros.
  destruct dbenv. simpl in H. lia. destruct dbenv. simpl in H. lia.
  exists (Nat.leb n0 n).
  constructor.
  * econstructor. lia. reflexivity.
  * econstructor. lia. reflexivity.
Qed.

Lemma maxTerminatesHelper_param0_leq_param1 :
  AbsEnv_prop_rel (CompilerAssumptionLogicTrans.aexp_terminates_always init_fenv 2)
   (CompilerAssumptionLogicTrans.bexp_terminates_always init_fenv 2)
   (AbsEnvLP (Dan_lp_bool (UnaryProp bool bexp_Dan (fun v : bool => v = true) (PARAM_Dan 0 <=d PARAM_Dan 1)))).
Proof.
  repeat constructor.
  unfold CompilerAssumptionLogicTrans.bexp_terminates_always.
  intros.
  destruct dbenv. simpl in H. lia. destruct dbenv. simpl in H. lia.
  exists (Nat.leb n n0).
  constructor.
  * econstructor. lia. reflexivity.
  * econstructor. lia. reflexivity.
Qed.

Lemma maxTerminatesHelper_param1_leq_param1 :
  AbsEnv_prop_rel (CompilerAssumptionLogicTrans.aexp_terminates_always init_fenv 2)
   (CompilerAssumptionLogicTrans.bexp_terminates_always init_fenv 2)
   (AbsEnvLP (Dan_lp_bool (UnaryProp bool bexp_Dan (fun v : bool => v = true) (PARAM_Dan 1 <=d PARAM_Dan 1)))).
Proof.
  repeat constructor.
  unfold CompilerAssumptionLogicTrans.bexp_terminates_always.
  intros.
  destruct dbenv. simpl in H. lia. destruct dbenv. simpl in H. lia.
  exists (Nat.leb n0 n0).
  constructor.
  * econstructor. lia. reflexivity.
  * econstructor. lia. reflexivity.
Qed.

Lemma maxTerminatesHelper1 :
  forall (b: bool),
  AbsEnv_prop_rel (CompilerAssumptionLogicTrans.aexp_terminates_always init_fenv 2)
   (CompilerAssumptionLogicTrans.bexp_terminates_always init_fenv 2)
   (AbsEnvLP
      (Dan_lp_bool
         (UnaryProp bool bexp_Dan (fun bval : bool => bval = b) ((PARAM_Dan 1 <=d PARAM_Dan 0) &d (PARAM_Dan 1 !=d PARAM_Dan 0))))).
Proof.
  repeat constructor.
  unfold CompilerAssumptionLogicTrans.bexp_terminates_always.
  intros.
  destruct dbenv. simpl in H. lia. destruct dbenv. simpl in H. lia.
  exists (andb (Nat.leb n0 n) (negb (andb (Nat.leb n0 n) (Nat.leb n n0)))).
  econstructor; econstructor; econstructor.
  lia. reflexivity. lia. reflexivity.
  all: constructor; constructor.
  all: try lia. all: reflexivity.
Qed.

Lemma maxTerminates :
  CompilerAssumptionLogicTrans.terminator init_fenv 2 Source.dan_log_true Source.max_conclusion maxSmallCompProg Source.maxSmallProof.
Proof.
  simpl.
  StackFrameMin.split_helper; StackFrameMin.split_helper. split.
  
  all: unfold  CompilerAssumptionLogicTrans.log_terminates_always.
  all: unfold Source.param0geqparam0, Source.param0geqparam1.
  all: unfold Source.param1geqparam0, Source.param1geqparam1.
  all: unfold Source.true_bool.
  all: unfold Source.param0gtparam1.
  all: unfold Source.notparam0gtparam1.
  all: unfold Source.dan_log_true.
  all: unfold Source.false_bool.
  all: unfold atrueDan.
  all: unfold afalseDan.
  all: unfold Source.true_bool.
  all: match goal with
       | [ |- _ /\ _ ] => split
       | _ => idtac
       end.
  all: match goal with
       | [ |- AbsEnv_prop_rel _ _ (AbsEnvAnd _ _ )] =>
           constructor
       | _ => idtac
       end.
  all: unfold geq_Dan.
  all: unfold gt_Dan.
  all: unfold lt_Dan.
  all: try eapply maxTerminatesHelper_max_conclusion.
  all: match goal with
       | [ |- AbsEnv_prop_rel _ _ (AbsEnvLP (Dan_lp_arith (TrueProp nat aexp_Dan)))] =>
           repeat constructor
       | _ => idtac
       end.
  all: try eapply maxTerminatesHelper_param0_leq_param0.
  all: try eapply maxTerminatesHelper_param1_leq_param0.
  all: try eapply maxTerminatesHelper_param0_leq_param1.
  all: try eapply maxTerminatesHelper_param1_leq_param1.
  all: try eapply maxTerminatesHelper1.
Qed.


From DanTrick Require Import ProofCompMod.

Module SourceMax <: SourceProgramType.
  Definition program := maxSmallCompProg.
  Definition precond := Source.dan_log_true.
  Definition postcond := Source.max_conclusion.
  Definition fenv := init_fenv.
  Definition hoare_triple := Source.maxSmallProof.
  Definition idents := maxSmallCompMap.
  Definition num_args := 2.
  Definition funcs := ((fenv "id") :: nil).
End SourceMax.

Module TargetMax := TargetProgram(SourceMax).


Require Import DanTrick.EnvToStack.

Module CompileMaxProofs <: CompileType.
  Module SOURCE := SourceMax.
  Module TARGET := TargetMax.
  Definition fenv_well_formed_proof := max_fenv_well_formed.
  Definition funcs_okay_too_proof := max_funcs_okay_too.
  Definition all_params_ok_for_funcs_proof := max_funcs_params_ok.
  Definition fun_app_well_formed_proof  := max_fun_app_imp.
  Definition aimp_always_wf_proof := maxSmallAimpAlwaysWf.

  Definition translate_precond_proof := maxSmallTranslation1.

  Definition translate_postcond_proof := maxSmallTranslation2.
  Definition terminator_proof := maxTerminates.
  Definition program_compiled_proof := eq_refl (comp_code maxSmallCompProg maxSmallCompMap 2).
  Definition fun_env_compiled_proof := eq_refl (compile_fenv init_fenv).
  Definition precond_wf_proof := maxSmallDanLogPropRel1.
  Definition postcond_wf_proof := maxSmallDanLogPropRel2.
  Definition imp_code_wf_proof := maxSmallVarMapWfWrtImp.
End CompileMaxProofs.

Print Source.maxSmallProof.

Module SmallerCompiler <: CompilerType.
  Definition proof_compiler := Tests.hl_compile_smaller.
End SmallerCompiler.

Module MaxSmallCompiled := CompileProof CompileMaxProofs SmallerCompiler.

(* Time Eval compute in MaxSmallCompiled.compiled. *)

From DanTrick Require Import StackLogic StackLanguage.
Local Example stack_pure_rel_var_stk2 :
  StackPurestBase.aexp_stack_pure_rel #(2) TargetMax.fenv.
Proof.
  constructor. auto.
Qed.

Local Example updater :
  state_update_rel 1 #(2)
    (AbsAnd
       (BaseState (AbsStkSize 3)
          (MetaBool
             (UnaryProp bool bexp_stack (fun v : bool => v = true)
                (comp_bool maxSmallCompMap (VAR_Dan "z" >=d PARAM_Dan 0)))))
       (BaseState (AbsStkSize 3)
          (MetaBool
             (UnaryProp bool bexp_stack (fun v : bool => v = true)
                (comp_bool maxSmallCompMap (VAR_Dan "z" >=d PARAM_Dan 1))))))
    (AbsAnd
       (BaseState (AbsStkSize 3)
                  (MetaBool
                     (UnaryProp bool bexp_stack (fun v : bool => v = true)
                                ((Var_Stk 2) <=s (Var_Stk 2))%bexp_stack)))
       (BaseState (AbsStkSize 3)
                  (MetaBool
                     (UnaryProp bool bexp_stack (fun v : bool => v = true)
                                ((Var_Stk 3) <=s (Var_Stk 2))%bexp_stack)))).
Proof.
  constructor.
      -- constructor; constructor; constructor; constructor.
         ++ simpl. Locate arith_update_rel. eapply UpVarStkNoMatch. unfold not. intros. invs H.
         ++ simpl. constructor. reflexivity.
         ++ constructor. simpl. auto.
         ++ constructor. simpl. auto.
         ++ auto.
      -- constructor; constructor; constructor; constructor; simpl.
         ++ eapply UpVarStkNoMatch. unfold not. intros. invs H.
         ++ constructor. reflexivity.
         ++ constructor. auto.
         ++ constructor. auto.
         ++ auto.
      -- constructor. auto.
      -- constructor. constructor. constructor. constructor; constructor; simpl; auto.
      -- constructor. constructor. constructor. unfold comp_bool. simpl. constructor; constructor; auto.
Qed.

Lemma absstate_match_rel_and_inversion :
  forall (A1 A2: AbsState) (fenv: fun_env_stk) (stk: stack),
  absstate_match_rel
        (AbsAnd A1 A2)
        fenv stk ->
  absstate_match_rel A1 fenv stk /\ absstate_match_rel A2 fenv stk.
Proof.
  intros. invs H.
  eauto.
Qed.

Lemma absstate_match_rel_basestate_inversion :
  forall (S: AbsStack) (B: MetavarPred) (fenv: fun_env_stk) (stk: stack),
    absstate_match_rel
        (BaseState S B)
        fenv stk ->
    absstack_match_rel S stk /\ meta_match_rel B fenv stk.
Proof.
  intros. invs H.
  eauto.
Qed.
Lemma absstate_match_rel_or_inversion :
  forall (A1 A2: AbsState) (fenv: fun_env_stk) (stk: stack),
  absstate_match_rel
        (AbsOr A1 A2)
        fenv stk ->
  absstate_match_rel A1 fenv stk \/ absstate_match_rel A2 fenv stk.
Proof.
  intros. invs H; [left | right ]; assumption.
Qed.

Lemma absstate_match_rel_inversion :
  (forall (S: AbsStack) (B: MetavarPred) (fenv: fun_env_stk) (stk: stack),
    absstate_match_rel
        (BaseState S B)
        fenv stk ->
    absstack_match_rel S stk /\ meta_match_rel B fenv stk) /\
  (forall (A1 A2: AbsState) (fenv: fun_env_stk) (stk: stack),
  absstate_match_rel
        (AbsAnd A1 A2)
        fenv stk ->
  absstate_match_rel A1 fenv stk /\ absstate_match_rel A2 fenv stk) /\
    (forall (A1 A2: AbsState) (fenv: fun_env_stk) (stk: stack),
  absstate_match_rel
        (AbsOr A1 A2)
        fenv stk ->
  absstate_match_rel A1 fenv stk \/ absstate_match_rel A2 fenv stk).
Proof.
  split; [ | split ]; [eapply absstate_match_rel_basestate_inversion | eapply absstate_match_rel_and_inversion | eapply absstate_match_rel_or_inversion ].
Qed.
    
  

Local Example max_target_proof_consequence :
  hl_stk
    (atruestk (((Var_Stk 3) <=s (Var_Stk 2)) &s (!s ((Var_Stk 3) <=s (Var_Stk 2)) &s ((Var_Stk 2) <=s (Var_Stk 3))))
       (BaseState (AbsStkSize 3) (MetaNat (TrueProp nat aexp_stack))))
    (Assign_Stk 1 #(2))
    (AbsAnd
       (BaseState (AbsStkSize 3)
          (MetaBool
             (UnaryProp bool bexp_stack (fun v : bool => v = true)
                (comp_bool maxSmallCompMap (VAR_Dan "z" >=d PARAM_Dan 0)))))
       (BaseState (AbsStkSize 3)
          (MetaBool
             (UnaryProp bool bexp_stack (fun v : bool => v = true)
                (comp_bool maxSmallCompMap (VAR_Dan "z" >=d PARAM_Dan 1))))))
    TargetMax.fenv.
Proof.
  eapply hl_stk_consequence with (Q := AbsAnd
       (BaseState (AbsStkSize 3)
          (MetaBool
             (UnaryProp bool bexp_stack (fun v : bool => v = true)
                (comp_bool maxSmallCompMap (VAR_Dan "z" >=d PARAM_Dan 0)))))
       (BaseState (AbsStkSize 3)
          (MetaBool
             (UnaryProp bool bexp_stack (fun v : bool => v = true)
                        (comp_bool maxSmallCompMap (VAR_Dan "z" >=d PARAM_Dan 1)))))).
  + econstructor.
    * eapply stack_pure_rel_var_stk2.
    * eapply updater.
  + unfold atruestk. unfold aimpstk; intros.
    eapply absstate_match_rel_inversion in H. destruct H.
    
    eapply absstate_match_rel_basestate_inversion in H, H0. destruct H, H0.
    invc H. invc H2. invc H1. invc H6. invc H5. invc H6.
    econstructor.
    * econstructor.
      -- constructor. assumption.
      -- constructor.
         ++ econstructor. invc H3.
            invs H7. invs H11. invs H12. invs H10.
            invs H17. invs H18.
            invs H14. invs H15. invs H19. invs H20. invs H21. invs H22. rewrite H30 in H24. invc H24. rewrite H33 in H27. invc H27. clear H6. clear H16. clear H25. clear H28 H32. clear H26. clear H31.
            econstructor. eassumption. eassumption. rewrite Nat.leb_refl. reflexivity. reflexivity.
         ++ constructor. constructor; constructor; auto.
    * constructor. constructor. assumption.
      constructor.
      -- invc H3. invc H7. invc H11. invc H12. invs H10. invs H9. invs H17. invc H18. invs H19. invs H20. invs H21. invs H22.
         rewrite H23 in H15. invc H15. rewrite H32 in H23. invc H23.
         rewrite H29 in H26. invc H26. invs H14. rewrite H27 in H29. invc H29. clear H3. clear H7 H11 H24 H28 H12. clear H18 H15. econstructor. eassumption.
         destruct (n1 <=? n3) eqn:?.
         ++ reflexivity.
         ++ simpl in H13. invs H13.
      -- constructor. constructor; constructor; auto.
  + unfold aimpstk; intros. assumption.
Qed.

Local Example max_target_proof_consequence' :
  hl_stk
    (AbsAnd (BaseState (AbsStkSize 3) (MetaNat (TrueProp nat aexp_stack)))
       (BaseState AbsStkTrue
          (MetaBool
             (UnaryProp bool bexp_stack (fun bval : bool => bval = false)
                (((Var_Stk 3) <=s (Var_Stk 2)) &s
                 (!s ((Var_Stk 3) <=s (Var_Stk 2)) &s ((Var_Stk 2) <=s (Var_Stk 3))))%bexp_stack))))
    (Assign_Stk 1 (Var_Stk 3))
    (AbsAnd
       (BaseState (AbsStkSize 3)
          (MetaBool
             (UnaryProp bool bexp_stack (fun v : bool => v = true)
                ((Var_Stk 2) <=s (Var_Stk 1))%bexp_stack)))
       (BaseState (AbsStkSize 3)
          (MetaBool
             (UnaryProp bool bexp_stack (fun v : bool => v = true)
                        ((Var_Stk 3) <=s (Var_Stk 1))%bexp_stack)))) TargetMax.fenv.
Proof.
  eapply hl_stk_consequence with (Q := AbsAnd
                 (BaseState (AbsStkSize 3)
                            (MetaBool
                               (UnaryProp bool bexp_stack (fun v : bool => v = true)
                                          ((Var_Stk 2) <=s (Var_Stk 1))%bexp_stack)))
                 (BaseState (AbsStkSize 3)
                            (MetaBool
                               (UnaryProp bool bexp_stack (fun v : bool => v = true)
                                          ((Var_Stk 3) <=s (Var_Stk 1))%bexp_stack)))).
    + econstructor.
      * constructor; auto.
      * constructor.
        -- econstructor.
           ++ econstructor. econstructor. econstructor.
              ** eapply UpVarStkNoMatch. unfold not. intros. invs H.
              ** econstructor. reflexivity.
           ++ econstructor. auto.
           ++ econstructor. econstructor. econstructor; econstructor; auto.
           ++ econstructor. auto.
        -- econstructor.
           ++ econstructor. econstructor. econstructor.
              ** eapply UpVarStkNoMatch. unfold not. intros. invs H.
              ** econstructor. reflexivity.
           ++ econstructor; auto.
           ++ econstructor; econstructor; econstructor; econstructor; auto.
           ++ econstructor; auto.
        -- econstructor; auto.
        -- econstructor; econstructor; econstructor; econstructor; constructor; auto.
        -- constructor. constructor. constructor. constructor; constructor; auto.
    + unfold aimpstk; intros.
      invc H. invc H5. invc H6. invc H0. invs H6. invs H9. invs H10. invs H8. invs H15. invs H16. invs H17. invs H18. invs H19. invs H20. invs H12. rewrite H31 in H22. invc H22. rewrite H34 in H31. invc H31. invs H13. rewrite H32 in H25. invc H25. rewrite H32 in H28. invc H28.
      constructor. constructor. constructor. assumption. constructor. econstructor.
      eassumption. destruct (n4 <=? n0) eqn:?. reflexivity.
      destruct (n0 <=? n4) eqn:?.
      simpl in H11. invs H11. simpl in H11. eapply Nat.leb_nle in Heqb.
      eapply not_le in Heqb. eapply gt_le_S in Heqb. clear H5 H23 H26. clear H14 H4. clear H27 H22. clear H30 H33. eapply le_Sn_le in Heqb. eapply Nat.leb_nle in Heqb0. congruence.
      constructor. constructor. constructor. auto. constructor. auto.
      constructor. constructor. assumption. constructor. econstructor. econstructor.
      eassumption. eassumption. rewrite Nat.leb_refl. reflexivity. reflexivity.
      constructor; constructor; constructor; auto.
    + unfold aimpstk. intros. auto.
Qed.

Local Example max_target_proof :
  hl_stk TargetMax.precond TargetMax.program TargetMax.postcond TargetMax.fenv.
Proof.
  unfold TargetMax.precond, TargetMax.program, TargetMax.postcond.
  unfold comp_code. unfold SourceMax.program. unfold maxSmallCompProg. simpl.
  unfold TargetMax.compile_dan_log, SourceMax.precond, SourceMax.postcond.
  unfold SourceMax.num_args, SourceMax.idents, Source.max_conclusion, Source.dan_log_true.
  simpl. econstructor.
  - constructor; constructor; constructor; constructor; constructor; auto.
  - eapply max_target_proof_consequence.
  - unfold afalsestk. unfold comp_bool. simpl.
    eapply max_target_proof_consequence'.
Qed.

