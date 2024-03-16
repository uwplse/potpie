From Coq Require Import List String Arith Psatz.


From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage FactEnvTranslator ProofCompAuto TerminatesForSure ProofCompCodeCompAgnosticMod ProofCompAutoAnother.
From Imp_LangTrick Require Import StackLangTheorems ImpVarMap ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed TranslationPure Imp_LangImpHigherOrderRelTheorems Imp_LangImpHigherOrderRel AimpWfAndCheckProofAuto.
From Imp_LangTrick Require Import SeriesExampleProofInputs.
From Imp_LangTrick Require Import SeriesExample.
From Imp_LangTrick Require Import EnvToStackLTtoLEQ.
Local Open Scope list_scope.
Local Open Scope string_scope.

Module SeriesProofCompilationOtherProofs(S: SeriesProgramInputs).
  Module CAPC := LTtoLEQCompilerAgnostic.

  Lemma precond_wf_proof :
    AbsEnv_prop_rel
      (var_map_wf_wrt_aexp
         ("dn"%string
              :: "rn"%string
              :: "i"%string
              :: "d"%string
              :: "rd"%string :: "dd"%string :: "x"%string :: nil))
      (var_map_wf_wrt_bexp
         ("dn"%string
              :: "rn"%string
              :: "i"%string
              :: "d"%string
              :: "rd"%string :: "dd"%string :: "x"%string :: nil))
      (series_precond S.x S.dn S.dd).
  Proof.
    AbsEnv_prop_wf_helper; simplify_var_map_wf_cases.
  Qed. 

  Lemma postcond_wf_proof :
    AbsEnv_prop_rel
      (var_map_wf_wrt_aexp
         ("dn"%string
              :: "rn"%string
              :: "i"%string
              :: "d"%string
              :: "rd"%string :: "dd"%string :: "x"%string :: nil))
      (var_map_wf_wrt_bexp
         ("dn"%string
              :: "rn"%string
              :: "i"%string
              :: "d"%string
              :: "rd"%string :: "dd"%string :: "x"%string :: nil))
      (series_postcond S.x S.dn S.dd).
  Proof.
    AbsEnv_prop_wf_helper; simplify_var_map_wf_cases.
  Qed. 



  Lemma imp_code_wf_proof :
    imp_rec_rel
      (var_map_wf_wrt_imp
         ("dn"%string
              :: "rn"%string
              :: "i"%string
              :: "d"%string
              :: "rd"%string :: "dd"%string :: "x"%string :: nil))
      (series_calculation_program S.x S.dn S.dd).
  Proof.
    eapply CompilerCorrectMoreHelpers.var_map_wf_imp_self_imp_rec_rel.
    reflexivity.
  Qed. 
  

  Lemma imp_has_variable_mult_ret :
    imp_has_variable (Ret (series_fenv "mult"))
                     (Imp_LangTrickLanguage.Body (series_fenv "mult")).
  Proof.
    ImpHasVariableReflection.prove_imp_has_variable.
  Qed.
  
  
  Lemma aimp_always_wf_proof : aimp_always_wf series_funcs
                                              (construct_trans (series_calculation_program S.x S.dn S.dd)) 0
                                              (series_precond S.x S.dn S.dd)
                                              (series_calculation_program S.x S.dn S.dd)
                                              (series_postcond S.x S.dn S.dd) series_fenv
                                              (series_program_facts S.x S.dn S.dd)
                                              (series_hoare_triple S.x S.dn S.dd).
  Proof.
    unfold construct_trans. simpl. 
    unfold aimp_always_wf.
    unfold series_calculation_program. unfold series_hoare_triple.
    unfold construct_trans.
    simpl.
    (* Set Ltac Profiling. *)
    
    hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases.
    
    - reflexivity.
    - hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; repeat econstructor.
    - hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases; repeat_econstructor_on.
      + hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; repeat econstructor.
      + hl_wf_seq_assign.
        hl_wf_seq_assign.
        hl_wf_seq_assign.
        unfold first_implication_hoare_triple.
        hl_wf_seq_assign.
        unfold eq_rect_r. simpl.
        
        hl_Imp_Lang_wf_roc_pre_helper; simplify_var_map_wf_cases; [ | | try log_Imp_Lang_wf_helper_no_app; repeat_econstructor_on .. ].
        -- simpl in Hnth. simpl.
           eapply first_implication_proof.
        -- rewrite UIP_option_refl. reflexivity.
        -- hl_Imp_Lang_wf_roc_post_helper; simplify_var_map_wf_cases; [ simpl | .. ]; [ | repeat_econstructor_on .. ]; try handle_fun_app_well_formed_app.
           unfold third_implication_hoare_triple.
           hl_imp_lang_wf_while_helper; simplify_var_map_wf_cases; repeat_econstructor_on.
           unfold while_body_proof.
           hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases; try finite_in_implication; try log_Imp_Lang_wf_helper_no_app; try handle_fun_app_well_formed_app; try repeat_econstructor_on.
           ++ hl_Imp_Lang_wf_roc_pre_helper; simplify_var_map_wf_cases; [ | | try finite_in_implication .. ].
              --- simpl. eapply second_implication_proof.
              --- rewrite UIP_option_refl. reflexivity.
              --- simpl. unfold second_implication_hoare_triple.
                  hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; try finite_in_implication.
                  +++ log_Imp_Lang_wf_helper_no_app.
                  +++ repeat econstructor.
                  +++ handle_fun_app_well_formed_app.
              --- 
                simpl. log_Imp_Lang_wf_helper_no_app; try handle_fun_app_well_formed_app; repeat_econstructor_on.
              --- simpl. log_Imp_Lang_wf_helper_no_app.
              --- log_Imp_Lang_wf_helper_no_app.
              --- simpl. repeat econstructor.
              --- simpl. repeat econstructor.
              --- simpl. repeat econstructor.
           ++ hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases; try finite_in_implication; repeat_econstructor_on; try handle_fun_app_well_formed_app.
              ** hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; try finite_in_implication; try log_Imp_Lang_wf_helper_no_app.
              ** 
                hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases; try finite_in_implication; repeat_econstructor_on; try handle_fun_app_well_formed_app.
                --- hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; try finite_in_implication; try log_Imp_Lang_wf_helper_no_app.
                --- hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; try log_Imp_Lang_wf_helper_no_app.
    - log_Imp_Lang_wf_helper_no_app.
    - log_Imp_Lang_wf_helper_no_app.
    - log_Imp_Lang_wf_helper_no_app.
    - repeat econstructor.
    - repeat econstructor.
    - repeat econstructor.
      (* Show Ltac Profile. *)
  Qed.  
End SeriesProofCompilationOtherProofs.
