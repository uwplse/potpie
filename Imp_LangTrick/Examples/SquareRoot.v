From Coq Require Import Psatz Arith String List ZArith.
From Coq Require Import QArith_base.
From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang.
From Imp_LangTrick Require Import ImpExampleHelpers ProofCompAutoAnother.
From Imp_LangTrick Require Import StackLangTheorems Imp_LangLogProp LogicProp.
From Imp_LangTrick Require Import Imp_LangLogHoare ProofCompMod SeriesExample ProofCompilableCodeCompiler EnvToStackLTtoLEQ ProofCompCodeCompAgnosticMod NotTerribleBImpLangInversion StackLanguage SeriesHelperCompilation AimpWfAndCheckProofAuto HelperFenvWF.

From Imp_LangTrick Require Export SquareRootCore SquareRootTreeCompiled SquareRootTreeCorrect.

From Imp_LangTrick.Tactics Require Import SemanTactics MiscTactics.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nat_scope.

Require Import FunctionWellFormed TranslationPure ParamsWellFormed ProofCompilerHelpers Imp_LangImpHigherOrderRel Imp_LangHoareWF CompilerAssumptionLogicTrans AimpWfAndCheckProofAuto ProofCompAuto StackFrameReflection.

  

Module SquareRootProofCompilation (S: SqrtProgramInputs).
  Module SQTPC := SquareRootTreeCorrect(S).
  Include SQTPC.
  Module ProofCompileSquareRoot <: ProgramProofCompilationType.
    Include SQTPC.
    (* Include SQTPC.TreeProofCompileSquareRoot. *)
    
    Lemma fact_cert : Imp_LangLogHoare.fact_env_valid SOURCE.facts SOURCE.fenv.
    Proof.
      unfold fact_env_valid; intros. invs H.
      - invs H0. eapply implication.
      - invs H0. 
        + invs H1. econstructor. repeat econstructor.
        + invs H1.
          * invs H2. econstructor. repeat econstructor.
          * invs H2.        
    Qed. 

    Lemma fenv_well_formed_proof : fenv_well_formed' SOURCE.funcs SOURCE.fenv.
    Proof.
      unfold SOURCE.funcs. unfold square_root_funcs.  
      apply big_fenv_well_formed. 
    Qed. 

    Lemma funcs_okay_too_proof : funcs_okay_too SOURCE.funcs TARGET.fenv.
    Proof.
      apply big_funcs_okay_too. 
    Qed. 

    Lemma all_params_ok_for_funcs_proof :
      Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func)
                                     (Imp_LangTrickLanguage.Body func))
             SOURCE.funcs.
    Proof.
      repeat econstructor. 
    Qed. 

    Lemma fun_app_well_formed_proof : fun_app_imp_well_formed SOURCE.fenv SOURCE.funcs SOURCE.program.
    Proof.
      unfold SOURCE.fenv, SOURCE.funcs, SOURCE.program.
      unfold sqrt_program. unfold square_root_program. simpl.
      FunctionWellFormedReflection.prove_fun_app_wf.
    Qed.

    Lemma imp_code_wf_proof : imp_rec_rel (var_map_wf_wrt_imp SOURCE.idents) SOURCE.program.
    Proof.
      eapply CompilerCorrectMoreHelpers.var_map_wf_imp_self_imp_rec_rel.
      reflexivity.
    Qed.    


    Ltac prove_funcs_okay_too_implies_ret_body :=
      match goal with
      | [ H: funcs_okay_too _ _ |- _ ] =>
          unfold funcs_okay_too in H; simpl in H; destruct H as (FORALL & _ & _);
          repeat match goal with
                 | [ H: Forall _ (_ :: _) |- _ ] =>
                     invc H
                 end;
          try match goal with
              | [ |- StackPurestBase.aexp_stack_pure_rel _ _ ] =>
                  eapply StackPurestBase.aexp_frame_implies_aexp_pure
              end
      end;
      match goal with
      | [ H: _ /\ StackFrameBase.aexp_frame_rule _ _ _ |- StackFrameBase.aexp_frame_rule _ _ _ ] =>
          eapply H
      | [ H: StackFrameBase.imp_frame_rule _ _ _ _ /\ _ |- StackFrameBase.imp_frame_rule _ _ _ _ ] =>
          eapply H
      end.


    Lemma funcs_okay_too_mult_body
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackFrameBase.imp_frame_rule (Body (fenv' "mult")) fenv'
                                    (Args (fenv' "mult"))
                                    (Return_pop (fenv' "mult") + Args (fenv' "mult")).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.


    Lemma funcs_okay_too_mult_return
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackFrameBase.aexp_frame_rule (Return_expr (fenv' "mult")) fenv'
                                     (Return_pop (fenv' "mult") + Args (fenv' "mult")).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    Lemma funcs_okay_too_mult_return_pure
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackPurestBase.aexp_stack_pure_rel (Return_expr (fenv' "mult")) fenv'.
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    Lemma funcs_okay_too_frac_sub_num_body
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackFrameBase.imp_frame_rule (Body (fenv' "frac_sub_numerator")) fenv'
                                    (Args (fenv' "frac_sub_numerator"))
                                    (Return_pop (fenv' "frac_sub_numerator") +
                                       Args (fenv' "frac_sub_numerator")).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.
    
    Lemma funcs_okay_too_frac_sub_num_return
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackFrameBase.aexp_frame_rule
        (Return_expr (fenv' "frac_sub_numerator")) fenv'
        (Return_pop (fenv' "frac_sub_numerator") +
           Args (fenv' "frac_sub_numerator")).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    Lemma funcs_okay_too_frac_sub_num_return_pure
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackPurestBase.aexp_stack_pure_rel
        (Return_expr (fenv' "frac_sub_numerator")) fenv'.
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.
    Lemma funcs_okay_too_frac_add_denom_body
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackFrameBase.imp_frame_rule (Body (fenv' "frac_add_denominator"))
                                    fenv' (Args (fenv' "frac_add_denominator"))
                                    (Return_pop (fenv' "frac_add_denominator") +
                                       Args (fenv' "frac_add_denominator")).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    

    Lemma funcs_okay_too_frac_add_denom_return
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackFrameBase.aexp_frame_rule
        (Return_expr (fenv' "frac_add_denominator")) fenv'
        (Return_pop (fenv' "frac_add_denominator") +
           Args (fenv' "frac_add_denominator")).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    Lemma funcs_okay_too_frac_add_denom_return_pure
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackPurestBase.aexp_stack_pure_rel
        (Return_expr (fenv' "frac_add_denominator")) fenv'.
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    Lemma funcs_okay_too_frac_add_num_body
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackFrameBase.imp_frame_rule (Body (fenv' "frac_add_numerator"))
                                    fenv' (Args (fenv' "frac_add_numerator"))
                                    (Return_pop (fenv' "frac_add_numerator") +
                                       Args (fenv' "frac_add_numerator")).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    

    Lemma funcs_okay_too_frac_add_num_return
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackFrameBase.aexp_frame_rule
        (Return_expr (fenv' "frac_add_numerator")) fenv'
        (Return_pop (fenv' "frac_add_numerator") +
           Args (fenv' "frac_add_numerator")).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    Lemma funcs_okay_too_frac_add_num_return_pure
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackPurestBase.aexp_stack_pure_rel
        (Return_expr (fenv' "frac_add_numerator")) fenv'.
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    Create HintDb square_root_hints.

    Local Hint Resolve funcs_okay_too_frac_add_denom_return_pure funcs_okay_too_frac_add_denom_return funcs_okay_too_frac_add_denom_body funcs_okay_too_frac_sub_num_return_pure funcs_okay_too_frac_sub_num_return funcs_okay_too_frac_sub_num_body funcs_okay_too_mult_return_pure funcs_okay_too_mult_return funcs_okay_too_mult_body funcs_okay_too_frac_add_num_return_pure funcs_okay_too_frac_add_num_return funcs_okay_too_frac_add_num_body : square_root_hints.

    Lemma check_proof_proof : CAPC.PC.check_proof SOURCE.fenv SOURCE.funcs SOURCE.precond SOURCE.postcond SOURCE.program SOURCE.facts SOURCE.idents SOURCE.num_args SOURCE.hoare_triple.
    Proof.
      cbn -[SOURCE.fenv SOURCE.funcs].
      unfold SOURCE.hoare_triple.
      unfold sqrt_triple. unfold hl_seq, hl_pre_nice, hl_post_nice.
      CAPC.PC.check_proof_helper.
      
      
      all: try (first [ eapply funcs_okay_too_mult_body | eapply funcs_okay_too_mult_return | eapply funcs_okay_too_mult_return_pure ]; eauto with square_root_hints).

      all: eauto with square_root_hints.

      all: repeat econstructor.
    Qed.

    Lemma translate_precond_proof : CAPC.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.precond = TARGET.precond.
    Proof.
      reflexivity.
    Qed.

    Lemma translate_postcond_proof : CAPC.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.postcond = TARGET.postcond.
    Proof.
      reflexivity.
    Qed.

    Lemma check_logic_precond_proof :
      CAPC.SC.check_logic SOURCE.precond = true.
    Proof.
      reflexivity.
    Qed.

    Lemma check_logic_postcond_proof :
      CAPC.SC.check_logic SOURCE.postcond = true.
    Proof.
      reflexivity.
    Qed.
    
    Lemma program_compiled_proof : TARGET.program = CAPC.CC.compile_imp SOURCE.program SOURCE.idents SOURCE.num_args.
    Proof.
      reflexivity.
    Qed.

    Lemma check_imp_proof :
      CAPC.CC.check_imp SOURCE.program = true.
    Proof.
      reflexivity.
    Qed.

    Lemma precond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.precond.
    Proof.
      AbsEnv_prop_wf_helper; simplify_var_map_wf_cases; cbn; finite_nodup.
    Qed.
    
    Lemma postcond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.postcond.
    Proof.
      AbsEnv_prop_wf_helper; simplify_var_map_wf_cases; cbn; finite_nodup.
    Qed.

    

    Lemma implication_transformer :  CAPC.PC.valid_imp_trans_def SOURCE.facts TARGET.facts SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
    Proof.
      econstructor. simpl; lia.
      split. 
      - intros.
        destruct n. simpl in H3. invs H3. reflexivity.
        destruct n. simpl in H3. invs H3. reflexivity.
        destruct n. simpl in H3. invs H3. reflexivity.
        destruct n. simpl in H3. discriminate. discriminate.
      - eapply stack_facts_valid.
    Qed.

    Lemma aimp_always_wf_proof : aimp_always_wf SOURCE.funcs SOURCE.idents SOURCE.num_args SOURCE.precond SOURCE.program SOURCE.postcond SOURCE.fenv SOURCE.facts SOURCE.hoare_triple.
    Proof.
      unfold aimp_always_wf. unfold SOURCE.hoare_triple. unfold sqrt_triple. unfold hl_seq, hl_pre_nice, hl_post_nice.
      simpl.
      unfold SOURCE.program. unfold sqrt_program. unfold square_root_program. simpl.
      unfold SOURCE.precond. unfold SOURCE.postcond.
      hl_Imp_Lang_wf_seq_helper; match goal with
                                 | [ |- log_Imp_Lang_wf _ _ _ ] =>
                                     try log_Imp_Lang_wf_helper_no_app
                                 | [ |- log_Imp_Lang_wf_map _ _ ] =>
                                     simplify_var_map_wf_cases
                                 | [ |- AbsEnv_prop_rel (all_params_ok_aexp SOURCE.num_args)
                                                       (all_params_ok_bexp SOURCE.num_args) _ ] =>
                                     repeat_econstructor_on
                                 | [ |- ProofCompilerBase.AbsEnv_prop_wf _ _ ] =>
                                     simplify_var_map_wf_cases
                                 | [ |- _ ] => idtac
                                 end.
      - eapply imp_code_wf_proof.
      - hl_imp_lang_wf_assign_helper; try simplify_var_map_wf_cases.
        cbn -[In].
        intros. finite_in_implication.
      - 
        
        hl_Imp_Lang_wf_seq_helper; smash_other_cases.
        + hl_imp_lang_wf_assign_helper; smash_other_cases.
          
          repeat econstructor.
        + hl_Imp_Lang_wf_seq_helper; smash_other_cases; try program_subset_imp_rec_rel_var_map_wf.
          * hl_imp_lang_wf_assign_helper; smash_other_cases; repeat_econstructor_on.
          * hl_Imp_Lang_wf_seq_helper; try hl_imp_lang_wf_assign_helper; smash_other_cases; repeat_econstructor_on.
            hl_Imp_Lang_wf_roc_post_helper; smash_other_cases.
            hl_imp_lang_wf_while_helper; smash_other_cases.

            hl_Imp_Lang_wf_if_helper; smash_other_cases.
            hl_Imp_Lang_wf_seq_helper; try hl_imp_lang_wf_assign_helper; smash_other_cases; repeat_econstructor_on.
            hl_Imp_Lang_wf_seq_helper; try hl_imp_lang_wf_assign_helper; smash_other_cases; repeat_econstructor_on.
            -- hl_Imp_Lang_wf_roc_pre_helper; smash_other_cases.
               ++ simpl. eapply anything_implies_true_prop.
               ++ rewrite UIP_option_refl. reflexivity.
               ++ simpl. hl_imp_lang_wf_assign_helper; smash_other_cases.
                  repeat econstructor.
            -- hl_Imp_Lang_wf_roc_pre_helper; smash_other_cases.
               ++ simpl. eapply anything_implies_true_prop.
               ++ simpl. rewrite UIP_option_refl. reflexivity.
               ++ simpl. hl_Imp_Lang_wf_seq_helper; try hl_imp_lang_wf_assign_helper; smash_other_cases; repeat_econstructor_on.
                  hl_Imp_Lang_wf_seq_helper; try hl_imp_lang_wf_assign_helper; smash_other_cases; repeat_econstructor_on.
    Qed.


  End ProofCompileSquareRoot.
End SquareRootProofCompilation.
