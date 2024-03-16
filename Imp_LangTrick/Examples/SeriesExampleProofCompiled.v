From Coq Require Import List String Arith Psatz.


From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage FactEnvTranslator ProofCompAuto TerminatesForSure ProofCompCodeCompAgnosticMod ProofCompAutoAnother.
From Imp_LangTrick Require Import StackLangTheorems ImpVarMap ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed TranslationPure Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems.
From Imp_LangTrick Require Import SeriesExampleProofInputs.
From Imp_LangTrick Require Import EnvToStackLTtoLEQ.
From Imp_LangTrick Require Import SeriesExample.
From Imp_LangTrick Require Import SeriesExampleProofCompiledOther
     SeriesHelperCompilation.
From Imp_LangTrick.Tactics Require Import MiscTactics.
From Imp_LangTrick Require Import StackFrameReflection StackPurestBaseReflection.
From Imp_LangTrick Require Export SeriesExampleTreeProofCompiled SeriesExampleTreeCorrect HelperFenvWF.

Local Open Scope string_scope.



Module SeriesProofCompilation(S: SeriesProgramInputs). (* <: ProgramProofCompilationType *)
  Module STC := SeriesTreeCorrect(S).
  Include STC.SPCPO.
  (* Include STC. *)
  
  
  Module SeriesActualProofCompilation2.
    Include STC.
    (* Include SPCPO.SeriesActualProofCompilation. *)
    Module SPCOP := SeriesProofCompilationOtherProofs(S).
    

    Lemma UIP_option_pair_refl (T: Type) (Huip_T: UIPList.UIP T) :
      forall (o: option (T * T))
        (H: o = o),
        H = eq_refl.
    Proof.
      pose proof (UIP_option := UIPList.UIP_to_option_pair).
      specialize (UIP_option _ Huip_T).
      unfold UIPList.UIP in UIP_option.
      intros. eapply UIP_option.
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


    Lemma pure_rel_mult_return_expr
          (fenv' : fun_env_stk)
          (H2 : funcs_okay_too
                  (Multiplication.prod_function
                     :: Exponentiation.exp_function
                     :: fraction_addition_denominator_fun
                     :: fraction_addition_numerator_fun
                     :: fraction_subtraction_numerator_fun
                     :: init_fenv "id"%string :: nil) fenv'):
      StackPurestBase.aexp_stack_pure_rel (Return_expr (fenv' "mult"%string))
                                          fenv'.
    Proof.
      intros. prove_funcs_okay_too_implies_ret_body.
    Qed.
    Lemma frame_rule_return_expr_mult (fenv' : fun_env_stk)
          (H2 : funcs_okay_too
                  (Multiplication.prod_function
                     :: Exponentiation.exp_function
                     :: fraction_addition_denominator_fun
                     :: fraction_addition_numerator_fun
                     :: fraction_subtraction_numerator_fun
                     :: init_fenv "id"%string :: nil) fenv'):
      StackFrameBase.aexp_frame_rule (Return_expr (fenv' "mult"%string)) fenv'
                                     (Return_pop (fenv' "mult"%string) + Args (fenv' "mult"%string)).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.
    
    Lemma frame_rule_body_mult (fenv' : fun_env_stk)
          (H2 : funcs_okay_too
                  (Multiplication.prod_function
                     :: Exponentiation.exp_function
                     :: fraction_addition_denominator_fun
                     :: fraction_addition_numerator_fun
                     :: fraction_subtraction_numerator_fun
                     :: init_fenv "id"%string :: nil) fenv'):
      StackFrameBase.imp_frame_rule (Body (fenv' "mult"%string)) fenv'
                                    (Args (fenv' "mult"%string))
                                    (Return_pop (fenv' "mult"%string) + Args (fenv' "mult"%string)).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.
    
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

    Lemma funcs_okay_too_exp_body
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackFrameBase.imp_frame_rule (Body (fenv' "exp"))
                                    fenv' (Args (fenv' "exp"))
                                    (Return_pop (fenv' "exp") +
                                       Args (fenv' "exp")).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    

    Lemma funcs_okay_too_exp_return
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackFrameBase.aexp_frame_rule
        (Return_expr (fenv' "exp")) fenv'
        (Return_pop (fenv' "exp") +
           Args (fenv' "exp")).
    Proof.
      prove_funcs_okay_too_implies_ret_body.
    Qed.

    Lemma funcs_okay_too_exp_return_pure
          (fenv': fun_env_stk)
          (OK : funcs_okay_too SOURCE.funcs fenv'):
      StackPurestBase.aexp_stack_pure_rel
        (Return_expr (fenv' "exp")) fenv'.
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

    Create HintDb funcs_okay_too_series.

    #[export]
     Hint Resolve funcs_okay_too_frac_add_denom_return_pure funcs_okay_too_frac_add_denom_return funcs_okay_too_frac_add_denom_body funcs_okay_too_frac_sub_num_return_pure funcs_okay_too_frac_sub_num_return funcs_okay_too_frac_sub_num_body funcs_okay_too_mult_return_pure funcs_okay_too_mult_return funcs_okay_too_mult_body funcs_okay_too_exp_return_pure funcs_okay_too_exp_return funcs_okay_too_exp_body funcs_okay_too_frac_add_num_return_pure funcs_okay_too_frac_add_num_return funcs_okay_too_frac_add_num_body : funcs_okay_too_series.
    #[export]
     Hint Resolve pure_rel_mult_return_expr frame_rule_return_expr_mult frame_rule_body_mult : funcs_okay_too_series.
    
    Ltac check_proof_while Hbody :=
      match goal with
      | [ |- CAPC.PC.check_proof _ _ ?d ?d' (WHILE_Imp_Lang ?b ?body) _ _ _ (hl_Imp_Lang_while ?d ?b ?body _ _ ?triple) ] =>
          let HeqP := fresh "HeqP" in
          assert (HeqP : afalseImp_Lang b d = d') by reflexivity || enough (HeqP : afalseImp_Lang b d = d');
          let Hi := fresh "Hi" in
          assert (Hi : WHILE_Imp_Lang b body = WHILE_Imp_Lang b body) by reflexivity;
          eapply CAPC.PC.CheckHLWhile with (hl__body := Hbody) (HeqP := HeqP) (Hi := Hi)
      end.

    Arguments LTtoLEQProofCompilable.SC.CC.compile_aexp _ _%list_scope _%nat_scope : simpl never. 
    Arguments StackLogic.aimpstk P Q fenv : simpl never.
    
    
    Lemma check_proof_proof : CAPC.PC.check_proof SOURCE.fenv SOURCE.funcs SOURCE.precond SOURCE.postcond SOURCE.program SOURCE.facts SOURCE.idents SOURCE.num_args SOURCE.hoare_triple.
    Proof.
      
      unfold SOURCE.fenv, SOURCE.funcs, SOURCE.precond, SOURCE.postcond, SOURCE.program, SOURCE.idents, SOURCE.num_args, SOURCE.hoare_triple. unfold series_fenv, series_funcs, series_calculation_program, construct_trans. simpl.
      unfold series_hoare_triple.

      CAPC.PC.check_proof_helper.
      (* all: intros; eauto with funcs_okay_too_series. *)
      (* repeat econstructor. repeat econstructor. *)
      (* all: repeat econstructor; eauto. rewrite <- H. simpl.  *)
      unfold eq_rect_r. simpl.
      CAPC.PC.check_proof_helper.
      unfold first_implication_hoare_triple.
      CAPC.PC.check_proof_helper.
      unfold third_implication_hoare_triple.
      CAPC.PC.check_proof_helper.

      all: eauto with funcs_okay_too_series.

      unfold while_body_proof.
      CAPC.PC.check_proof_helper. unfold second_implication_hoare_triple.
      CAPC.PC.check_proof_helper.
      repeat econstructor.
      repeat econstructor.
      all: eauto with funcs_okay_too_series.
      all: repeat econstructor.
    Qed.
    
    
    
    
    
    
    Lemma fact_cert : Imp_LangLogHoare.fact_env_valid SOURCE.facts SOURCE.fenv.
    Proof.
      eapply SeriesExample.fact_cert.
    Qed.

    Lemma fun_app_well_formed_mult :
      fun_app_imp_well_formed
        SOURCE.fenv
        SOURCE.funcs 
        Multiplication.prod_body.
    Proof.
      unfold SOURCE.fenv. unfold SOURCE.funcs. unfold series_funcs. unfold series_fenv.
      unfold Multiplication.prod_body. FunctionWellFormedReflection.prove_fun_app_wf.
    Qed.

    Lemma fun_app_well_formed_exp :
      fun_app_imp_well_formed
        SOURCE.fenv
        SOURCE.funcs
        Exponentiation.exp_body.
    Proof.
      unfold Exponentiation.exp_body. FunctionWellFormedReflection.prove_fun_app_wf.
    Qed.

    

    Lemma args_wf_implies_fun_app_mult_wf :
      forall (a1 a2: aexp_Imp_Lang),
        fun_app_args_well_formed SOURCE.fenv SOURCE.funcs (a1 :: a2 :: nil) ->
        fun_app_well_formed SOURCE.fenv SOURCE.funcs
                            (APP_Imp_Lang "mult"%string
                                          (a1 :: a2 :: nil)).
    Proof.
      intros.
      simpl. invs H. invs H5.
      econstructor.
      - assumption.
      - reflexivity.
      - unfold SOURCE.funcs.  unfold series_funcs. cbn -[In]. finite_in.
      - reflexivity.
      - ImpHasVariableReflection.prove_imp_has_variable.
      - left. reflexivity.
    Qed.

    Lemma args_wf_implies_fun_app_exp_wf :
      forall (a1 a2: aexp_Imp_Lang),
        fun_app_args_well_formed SOURCE.fenv SOURCE.funcs (a1 :: a2 :: nil) ->
        fun_app_well_formed SOURCE.fenv SOURCE.funcs
                            (APP_Imp_Lang "exp"%string
                                          (a1 :: a2 :: nil)).
    Proof.
      intros. econstructor.
      - assumption.
      - reflexivity.
      - unfold SOURCE.fenv. unfold SOURCE.funcs. unfold series_fenv. unfold series_funcs. cbn -[In]. finite_in.
      - reflexivity.
      - ImpHasVariableReflection.prove_imp_has_variable.
      - left. reflexivity.
    Qed.
    

    Lemma fun_app_well_formed_frac_add_denominator :
      fun_app_imp_well_formed
        SOURCE.fenv
        SOURCE.funcs
        fraction_addition_denominator_fun_body.
    Proof.
      FunctionWellFormedReflection.prove_fun_app_wf.
    Qed.

    Lemma fun_app_well_formed_frac_add_numerator :
      fun_app_imp_well_formed
        SOURCE.fenv
        SOURCE.funcs
        fraction_addition_numerator_fun_body.
    Proof.
      FunctionWellFormedReflection.prove_fun_app_wf.
    Qed.

    
    
    
    Lemma fenv_well_formed_proof : fenv_well_formed' SOURCE.funcs SOURCE.fenv.
    Proof.
      unfold fenv_well_formed'. unfold SOURCE.funcs. unfold series_funcs. unfold SOURCE.fenv. unfold series_fenv.
      repeat split.
      - finite_nodup.
      - simpl in H. (* I forget how to do this one nicely...if it can be done *)
        simpl. unfold update in H.
        
        string_dec_destruct_context; rewrite H; simpl.
        + left. left. reflexivity.
        + left. right. left. reflexivity.
        + left. right. right. left. reflexivity.
        + left. right. right. right. left. reflexivity.
        + left. right. right. right. right. left. reflexivity.
        + right. unfold init_fenv. reflexivity.
        + right. unfold init_fenv. reflexivity.
      - simpl.
        simpl in H. unfold update in H.
        string_dec_destruct_context; rewrite H; simpl.
        + eapply fun_app_well_formed_mult.
        + eapply fun_app_well_formed_exp. 
        + eapply fun_app_well_formed_frac_add_denominator.
        + eapply fun_app_well_formed_frac_add_numerator.
        + FunctionWellFormedReflection.prove_fun_app_wf.
        + econstructor. econstructor.
        + FunctionWellFormedReflection.prove_fun_app_wf.
      - simpl in H. rewrite H. unfold update. destruct (string_dec "mult" f).
        + rewrite <- e in H. unfold update in H. simpl in H. simpl.
          ImpHasVariableReflection.prove_imp_has_variable.
        + destruct (string_dec "exp" f).
          * simpl. ImpHasVariableReflection.prove_imp_has_variable.
          * 
            string_dec_destruct; simpl; try ImpHasVariableReflection.prove_imp_has_variable.
      - simpl. finite_nodup.
      - intros. simpl in *. rewrite H0 in *.
        unfold update in *.
        string_dec_destruct; simpl; try congruence.
        + unfold init_fenv in H. destruct H as [H | [H | [H | [H | [H | [ H | H ]]]]]]; try invs H.
          destruct IN_FUNC_NAMES as [I | [I | [I | [I | [I | [ I | I ]]]]]]; try contradiction.
      - finite_in.
      -  simpl. unfold update. intros.
         string_dec_destruct.
         + get_contradiction.
           left. assumption.
         + get_contradiction. right. left. assumption.
         + get_contradiction. right. right. left. assumption.
         + get_contradiction. right. right. right. left. assumption.
         + get_contradiction. right. right. right. right. left. assumption.
         + simpl. unfold init_fenv. reflexivity.
         + reflexivity.
      - simpl. unfold update. intros.
        string_dec_destruct.
        + exists "mult"%string.
          repeat split.
          * left. reflexivity.
          * rewrite H. reflexivity.
        + exists "exp"%string.
          repeat split.
          * intuition.
          * rewrite H. reflexivity.
        + exists "frac_add_denominator"%string.
          rewrite H. intuition.
        + exists "frac_add_numerator"%string. rewrite H. intuition.
        + exists "frac_sub_numerator"%string. rewrite H. intuition.
        + exists "id"%string. rewrite H. intuition.
          
        + exists "id"%string. rewrite H. simpl. intuition.
    Qed.
    
    Lemma funcs_okay_too_proof : funcs_okay_too SOURCE.funcs TARGET.fenv.
    Proof.
      unfold TARGET.fenv. apply big_funcs_okay_too. 
    Qed.
    
    
    Lemma all_params_ok_for_funcs_proof :
      Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func)
                                        (Imp_LangTrickLanguage.Body func))
             SOURCE.funcs.
    Proof.
      unfold SOURCE.funcs. unfold series_funcs.
      repeat econstructor.
    Qed.

    Axiom UIP_AbsEnv_Pair :
      forall (A B: AbsEnv * AbsEnv)
             (H1 H2: A = B),
        H1 = H2.
    Lemma UIP_AbsEnv_Pair_refl :
      forall (A: AbsEnv * AbsEnv)
             (H: A = A),
        H = eq_refl.
    Proof.
      intros.
      pose proof (UIP_AbsEnv_Pair).
      specialize (H0 A A H eq_refl). assumption.
    Qed.
    
    
    Lemma fun_app_well_formed_proof : fun_app_imp_well_formed SOURCE.fenv SOURCE.funcs SOURCE.program.
    Proof.
      unfold SOURCE.fenv, SOURCE.funcs, SOURCE.program. unfold series_fenv, series_funcs. simpl. unfold series_calculation_program.
      simpl.
      unfold lt_Imp_Lang. unfold neq_Imp_Lang. unfold eq_Imp_Lang.
      FunctionWellFormedReflection.prove_fun_app_wf.
    Qed.

    
    
    Lemma aimp_always_wf_proof : aimp_always_wf SOURCE.funcs SOURCE.idents SOURCE.num_args SOURCE.precond SOURCE.program SOURCE.postcond SOURCE.fenv SOURCE.facts SOURCE.hoare_triple.
    Proof.
      unfold SOURCE.funcs, SOURCE.idents, SOURCE.num_args, SOURCE.precond, SOURCE.program, SOURCE.postcond, SOURCE.fenv, SOURCE.facts, SOURCE.hoare_triple. unfold SOURCE.x, SOURCE.dn, SOURCE.dd.
      eapply SPCOP.aimp_always_wf_proof.
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
      unfold SOURCE.idents. unfold construct_trans. simpl. unfold SOURCE.precond. unfold SOURCE.x, SOURCE.dn, SOURCE.dd.
      eapply SPCOP.precond_wf_proof.
    Qed.

    Lemma postcond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.postcond.
    Proof.
      unfold SOURCE.idents. unfold construct_trans. simpl. unfold SOURCE.postcond. unfold SOURCE.x, SOURCE.dn, SOURCE.dd.
      eapply SPCOP.postcond_wf_proof.
    Qed.


    Lemma imp_code_wf_proof : imp_rec_rel (var_map_wf_wrt_imp SOURCE.idents) SOURCE.program.
    Proof.
      unfold SOURCE.idents, SOURCE.program.
      unfold construct_trans. simpl. unfold SOURCE.x, SOURCE.dn, SOURCE.dd.
      eapply SPCOP.imp_code_wf_proof.
    Qed.


    Lemma implication_transformer :  CAPC.PC.valid_imp_trans_def SOURCE.facts TARGET.facts SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
    Proof.
      unfold SOURCE.facts, SOURCE.fenv, TARGET.facts, TARGET.fenv, SOURCE.idents, SOURCE.num_args.
      unfold SOURCE.x, SOURCE.dn, SOURCE.dd, SeriesTargetProgramInputs.target_facts, SOURCE.program.
      unfold SeriesTargetProgramInputs.target_fenv.
      unfold SeriesSourceProgram.facts.
      unfold SeriesSourceProgram.x, SeriesSourceProgram.dd, SeriesSourceProgram.dn, SeriesSourceProgram.funcs, SOURCE.x, SOURCE.dn, SOURCE.dd.
      unfold CAPC.PC.valid_imp_trans_def. simpl.
      repeat split.
      - reflexivity.
      - intros.
        match goal with
        | [ H: CAPC.PC.SC.comp_logic 0 (construct_trans ?a) _ = _ |- _ ] =>
            remember (construct_trans a) as idents
        end.
        unfold series_program_facts in H3.
        Print CAPC.PC.SC.comp_logic.
        #[local] Arguments CAPC.PC.SC.comp_logic _%nat_scope _%list_scope _/.
        destruct n; simpl in H3.
        + invs H3. reflexivity.
        + destruct n; simpl in H3.
          * invs H3. reflexivity.
          * destruct n; simpl in H3; invs H3. reflexivity.
            rewrite nth_error_nil_none in H3. invc H3.
      - eapply stack_fact_env_valid.
    Qed. 
  End SeriesActualProofCompilation2.
End SeriesProofCompilation.

