From Coq Require Import Psatz Arith String List ZArith.
From Coq Require Import QArith_base.
From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang.
From Imp_LangTrick Require Import ImpExampleHelpers ProofCompAutoAnother.
From Imp_LangTrick Require Import StackLangTheorems Imp_LangLogProp LogicProp.
From Imp_LangTrick Require Import Imp_LangLogHoare ProofCompMod SeriesExample ProofCompilableCodeCompiler EnvToStackLTtoLEQ ProofCompCodeCompAgnosticMod NotTerribleBImpLangInversion StackLanguage SeriesHelperCompilation.

From Imp_LangTrick.Tactics Require Import SemanTactics MiscTactics.
From Imp_LangTrick Require Import SquareRootCore.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nat_scope.

Require Import FunctionWellFormed TranslationPure ParamsWellFormed ProofCompilerHelpers Imp_LangImpHigherOrderRel Imp_LangHoareWF CompilerAssumptionLogicTrans AimpWfAndCheckProofAuto ProofCompAuto HelperWrappers.



Module Type SqrtProgramInputs.
  Parameter a b epsilon_n epsilon_d : nat.
End SqrtProgramInputs.


Module SquareRootTreeProofCompilation (S: SqrtProgramInputs).
  Module SqrtSource <: SourceProgramType.
    Include S.
    Definition program := sqrt_program a b epsilon_n epsilon_d.
    Definition precond := (AbsEnvLP
                             (Imp_Lang_lp_arith (TrueProp _ _ ))). 
    Definition postcond := sqrt_postcond a b epsilon_n epsilon_d.
    Definition fenv := square_root_fenv.
    Definition facts := sqrt_facts'' a b epsilon_n epsilon_d.
    Definition hoare_triple := sqrt_triple a b epsilon_n epsilon_d.
    Definition idents := construct_trans program.
    Definition num_args := 0.
    Definition funcs := (prod_function
                           :: exp_function
                           :: fraction_addition_denominator_fun
                           :: fraction_addition_numerator_fun
                           :: fraction_subtraction_numerator_fun
                           :: init_fenv "id" :: nil). 
  End SqrtSource.

  Module SqrtTargetInputs <: TargetProgramInputs.
    Definition target_fenv : fun_env_stk := (compile_fenv square_root_fenv).
    Definition target_facts idents args :=
      map (fun (x: (AbsEnv * AbsEnv)) =>
             let (P, Q) := x in
             let cl := LTtoLEQCompilerAgnostic.SC.comp_logic args idents in
             (cl P, cl Q))
          SqrtSource.facts.
  End SqrtTargetInputs.

  Module SqrtTarget := CompilerAgnosticProofCompilableTargetProgram (SqrtSource) (LTtoLEQCompilerAgnostic.PC.CC) (LTtoLEQCompilerAgnostic.PC.SC) (SqrtTargetInputs).

  Module TreeProofCompileSquareRoot.
    Module CAPC := LTtoLEQCompilerAgnostic.
    Module SOURCE := SqrtSource.
    Module TARGET := SqrtTarget.

    Lemma pre_sound : CAPC.SC.transrelation_sound SOURCE.precond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
    Proof.
      econstructor. intros. split; intros.
      - simpl. destruct_stks stk. meta_smash.
        + unfold SOURCE.num_args in H. simpl. lia.
        + unfold SOURCE.precond, sqrt_precond in H1. 
          invc H1. invc H3. invc H2. intuition.
      (* + repeat econstructor. *)
      - invc H1. invc H4. invc H7. invc H3. repeat econstructor; intuition.
    Qed.

    Lemma post_sound : CAPC.SC.transrelation_sound SOURCE.postcond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
    Proof.
      econstructor. intros. split; intros.
      - simpl. destruct_stks stk. meta_smash.
        + unfold SOURCE.num_args in H. simpl. lia.
        + unfold SOURCE.postcond, sqrt_postcond in H1.
          unfold sqrt_postcond_prop.  
          invc H1. invc H3. invc H2. invc H6. invc H7.
          unfold sqrt_postcond_prop in H8. 
          intuition.
        + repeat econstructor.
      - invc H1. invc H4. invc H7. invc H3. invc H4. invc H8. invc H9. 
        destruct_stks stk. 
        simpl in H13, H15. invs H13. invs H15.
        econstructor. econstructor. econstructor. econstructor. reflexivity. econstructor. reflexivity.
        assumption.       
    Qed.

    Lemma stack_facts_valid :
      StackLogic.fact_env_valid TARGET.facts TARGET.fenv.
    Proof.
      unfold StackLogic.fact_env_valid.
        intros. invs H; simpl in H0.   
        + invs H0.
          econstructor. invs H1. invs H4. eassumption.
          invs H1. invs H4. invs H5.
          do 4 make_stack_big_enough.
          invs H1. invs H4.
          unfold LTtoLEQProofCompilable.SC.CC.compile_bexp, LTtoLEQProofCompilable.SC.CC.compile_aexp in *. cbn [compile_aexp compile_bexp] in *.
          (* simpl in *. *)
          invs H7.   
          invs H16.
          invs H6.
          invs H18.
          invs H22.
          invs H26.
          assert (aexp_stack_sem
                    ("mult" @s
                            ("mult" @s (Var_Stk 1) :: (Var_Stk 1) :: nil)%aexp_stack
                            :: ("mult" @s (Const_Stk SqrtSource.b) :: (Const_Stk SqrtSource.epsilon_n) :: nil)%aexp_stack
                            :: nil) TARGET.fenv (n :: n0 :: n1 :: n2 :: stk) (
                      (n :: n0 :: n1 :: n2 :: stk), ((n * n) * (SqrtSource.b * SqrtSource.epsilon_n)))) as oobn.
          { unfold TARGET.fenv. unfold SqrtTargetInputs.target_fenv. 
            eapply target_mult_aexp_wrapper.  
            eapply target_mult_aexp_wrapper.
            econstructor; simpl; try lia; try reflexivity. 
            econstructor; simpl; try lia; try reflexivity.
            eapply target_mult_aexp_wrapper.
            econstructor.
            econstructor.
          }
          assert ((stk'0, n3) = 
                    (n :: n0 :: n1 :: n2 :: stk,
                      n * n * (SqrtSource.b * SqrtSource.epsilon_n))).
          {
            eapply aexp_stack_sem_det; eassumption.
          }
          invs H2; clear H2.
          assert (aexp_stack_sem
                    ("mult" @s
                            ("mult" @s (Var_Stk 4) :: (Var_Stk 4) :: nil)%aexp_stack
                            :: ("mult" @s (Const_Stk SqrtSource.b) :: (Const_Stk SqrtSource.epsilon_d) :: nil)%aexp_stack
                            :: nil) TARGET.fenv (n :: n0 :: n1 :: n2 :: stk) (
                      (n :: n0 :: n1 :: n2 :: stk), ((n2 * n2) * (SqrtSource.b * SqrtSource.epsilon_d)))) as ffbd.
          { eapply target_mult_aexp_wrapper.  
            eapply target_mult_aexp_wrapper.
            econstructor; simpl; try lia; try reflexivity. 
            econstructor; simpl; try lia; try reflexivity.
            eapply target_mult_aexp_wrapper.
            econstructor.
            econstructor.
          }
          assert ((stk1, n5) = (n :: n0 :: n1 :: n2 :: stk,
                                 n2 * n2 * (SqrtSource.b * SqrtSource.epsilon_d))).
          { eapply aexp_stack_sem_det; eassumption. }
          
          invs H2; clear H2.
          assert (aexp_stack_sem
                    ("mult" @s
                            ("mult" @s (Var_Stk 1) :: (Var_Stk 1) :: nil)%aexp_stack
                            :: ("mult" @s (Const_Stk SqrtSource.a) :: (Const_Stk SqrtSource.epsilon_d) :: nil)%aexp_stack
                            :: nil) TARGET.fenv (n :: n0 :: n1 :: n2 :: stk) (
                      (n :: n0 :: n1 :: n2 :: stk), ((n * n) * (SqrtSource.a * SqrtSource.epsilon_d)))) as ooad.
          { eapply target_mult_aexp_wrapper.  
            eapply target_mult_aexp_wrapper.
            meta_smash.
            meta_smash.
            eapply target_mult_aexp_wrapper; meta_smash.
          }
          assert ((stk', n6) = (n :: n0 :: n1 :: n2 :: stk,
                                 n * n * (SqrtSource.a * SqrtSource.epsilon_d))) by (eapply aexp_stack_sem_det; eassumption).
          invs H2; clear H2.
          clear H21 H28 H25 H22.
          invs H23. 
          invs H25. 
          assert ((stk', n3) = 
                    (n :: n0 :: n1 :: n2 :: stk,
                      n * n * (SqrtSource.b * SqrtSource.epsilon_n))) by (eapply aexp_stack_sem_det; eassumption).
          invs H2; clear H2.
          assert ((stk1, n5) = (n :: n0 :: n1 :: n2 :: stk,
                                 n * n * (SqrtSource.a * SqrtSource.epsilon_d))) by (eapply aexp_stack_sem_det; eassumption).
          invs H2; clear H2.
          assert ((n :: n0 :: n1 :: n2 :: stk, n6) = (n :: n0 :: n1 :: n2 :: stk,
                                                   n2 * n2 * (SqrtSource.b * SqrtSource.epsilon_d))) by (eapply aexp_stack_sem_det; eassumption).
          invs H2; clear H2.
          meta_smash.
          unfold sqrt_postcond_prop. 
          clear H21 H28 H22 H25 ooad ffbd oobn H23 H26 H18 H13.
          symmetry in H24.
          rewrite Bool.orb_false_iff in H24.
          destruct H24.
          rewrite leb_iff_conv in H2.
          rewrite leb_iff_conv in H13.
          split; lia.
          repeat econstructor. 
        + simpl in *. invs H0.
          * invs H1. econstructor.
            invs H2. invs H8. apply H6.
            meta_smash; econstructor.
          * invs H1; try contradiction. invs H2.
            econstructor. invs H3. invs H9. eassumption.
            meta_smash.
            econstructor.
    Qed.
  End TreeProofCompileSquareRoot.
End SquareRootTreeProofCompilation.

