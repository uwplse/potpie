From Coq Require Import Psatz Arith String List.

From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang SeriesExample FunctionWellFormed EnvToStackLTtoLEQ TranslationPure ProofCompMod StackLangTheorems ParamsWellFormed Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems Imp_LangDec Imp_LangLogPropDec UIPList StackLanguage.

Local Open Scope list_scope.
Local Open Scope string_scope.
From Imp_LangTrick Require Import ProofCompAutoAnother BloomFilterArrayProgram.
From Imp_LangTrick Require Import LogicProp Imp_LangLogProp Imp_LangLogHoare  ProofCompAuto ProofCompCodeCompAgnosticMod AimpWfAndCheckProofAuto StackLangTheorems Multiplication MultiplicationTreeCompiled MultiplicationCompiled HelperFenvWF MultWrappers.
Local Open Scope imp_langtrick_scope.




Module SourceExp <: SourceProgramType.
  Definition program := exp_body.
  Definition precond := true_precondition.
  Definition postcond := exp_postcondition.
  Definition fenv := series_fenv.
  Definition facts := exp_facts. 
  Definition hoare_triple := (partial_exp_correct series_fenv eq_refl).
  Definition idents := prod_comp_map.
  Definition num_args := 2.
  Definition funcs := (prod_function :: exp_function :: fraction_addition_denominator_fun :: fraction_addition_numerator_fun :: fraction_subtraction_numerator_fun ::
  (init_fenv "id") :: nil).
End SourceExp.


Module TargetExp <: TargetProgramType. 
  Module CAPC := LTtoLEQCompilerAgnostic.
  Module SP := SourceExp.
  Definition compile_imp_lang_log (d: AbsEnv):=
    CheckableLTtoLEQSpec.comp_logic SP.num_args SP.idents d.
  Definition program: imp_stack := compile_imp SP.program (fun x => one_index_opt x SP.idents) SP.num_args.
  Definition precond := CAPC.SC.comp_logic SP.num_args SP.idents SP.precond.
  Definition postcond := CAPC.SC.comp_logic SP.num_args SP.idents SP.postcond.
  Definition fenv: fun_env_stk := (compile_fenv series_fenv).
  Definition facts := map 
  (fun p => 
  match p with 
  |(x, y) => ((CAPC.SC.comp_logic SP.num_args SP.idents x), (CAPC.SC.comp_logic SP.num_args SP.idents y))
  end)
  SP.facts.
End TargetExp.

Module CompileExpTreeOnly.
  Module CAPC := LTtoLEQCompilerAgnostic.
  Module SOURCE := SourceExp.
  Module TARGET := TargetExp.

  Ltac unfold_src_tar := unfold SOURCE.idents, SOURCE.precond, SOURCE.program, SOURCE.postcond, SOURCE.fenv, SOURCE.hoare_triple, SOURCE.num_args, SOURCE.funcs, TARGET.precond, TARGET.postcond, TARGET.program, TARGET.compile_imp_lang_log, TARGET.fenv in *.

  Ltac unfold_idents := unfold SOURCE.idents in *; unfold prod_comp_map in *.

 

  Lemma pre_sound : CAPC.SC.transrelation_sound SOURCE.precond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold_src_tar. constructor. intros. split.
    - intros. simpl. 
      inversion H1; subst. inversion H3; subst. 
      inversion H4; subst. inversion H9; subst. 
      inversion H8; subst. 
      econstructor.
      + inversion H0; subst. simpl. econstructor. simpl. 
        lia.
      + inversion H0; subst. econstructor. econstructor;
        econstructor; try lia.
        * simpl. lia.  
        * simpl. apply H11.
        * simpl. lia.
        * simpl. apply H6.
        * repeat econstructor.       
    - unfold SourceProd.num_args in H. econstructor.
      inversion H1; subst. inversion H4; subst.
      inversion H0; subst. inversion H7; subst. 
      inversion H5; subst. inversion H11; subst.
      simpl in *.
      inversion H12; subst. simpl in *.       
      repeat econstructor; try lia.
      apply H16. apply H19.    
  Defined.

  Lemma post_sound : CAPC.SC.transrelation_sound SOURCE.postcond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold_src_tar. unfold compile_fenv. unfold series_fenv. unfold imp_fenv_ify. simpl. constructor; split; intros; simpl. 
    - invs H0. simpl in H0. invs H1. invs H3. invs H4. invs H9.
      invs H10. invs H11. simpl. 
      econstructor. econstructor. simpl. lia.
      econstructor. econstructor. econstructor; try simpl; try lia. 
      apply H6. econstructor; try simpl; try lia. apply H8.
      econstructor. simpl. lia. simpl. lia. simpl. exists. apply H12.
      repeat econstructor.
    - invs H0. simpl in H0. invs H1. invs H7. invs H3. invs H11.
      invs H12. invs H13. simpl in *.
      econstructor. econstructor. econstructor.
      + econstructor. lia. apply H16.
      + econstructor. lia. apply H19.
      + econstructor.  exists.
      + invs H22. apply H14.            
  Defined.

  Lemma exp_stack_facts_valid :
    StackLogic.fact_env_valid TARGET.facts TARGET.fenv.
  Proof.
    unfold StackLogic.fact_env_valid. intros.  
    unfold TARGET.facts in H. simpl in H.
    destruct H. 
    + invs H. econstructor.
      invs H0. eassumption.
      invs H0. invs H6. invs H2. econstructor. econstructor. econstructor. eassumption. econstructor. eassumption.
      econstructor. eassumption. 
      econstructor. econstructor. econstructor.
      unfold exp_invariant_prop. simpl. split.
      assert (v1 - v1 = 0) by lia. rewrite H1. simpl. lia. lia.   
      repeat econstructor.
    + invs H.
      * invs H0. unfold LTtoLEQProofCompilable.SC.CC.compile_aexp in *. simpl in *. clear H.
        econstructor. invs H. inv H3. 
        econstructor. invs H. invs H3. invs H8. invs H2. invs H10. 
        invs H14. invs H16. invs H18.
        econstructor. econstructor. eassumption.
        econstructor. eassumption.
        econstructor. econstructor. eassumption. econstructor.
        econstructor. unfold TARGET.fenv. unfold compile_fenv. 
        unfold series_fenv. unfold imp_fenv_ify. unfold update.
        pose proof target_mult_aexp_wrapper stk (Var_Stk 1) (Var_Stk 4) val2 val0. eapply H1; try eassumption.
        econstructor.
        unfold exp_invariant_prop in H11. simpl in H11.
        unfold exp_invariant_prop. simpl.   
        destruct H11; split; try lia. 
        invs H6.
        invs H23. invs H9. invs H24. 
        assert (stk = stk') by (invs H28; reflexivity).
        rewrite H1 in *.  
        assert (n2 = val1).
        pose proof aexp_stack_sem_det TARGET.fenv stk' (Var_Stk 2) (stk', n2) (stk', val1) H29 H15. 
        invs H21. reflexivity.
        rewrite H21 in *. 
        assert ((val - (val1 - 1)) = 1 + (val - val1)).
        simpl. symmetry in H30. 
        eapply leb_complete in H30.
        invs H28. 
        lia.
        rewrite H22. simpl. lia.
        repeat econstructor.       
      * clear H. destruct H0; try contradiction. 
        invs H; clear H. econstructor.
        invs H. invs H5. assumption.
        unfold LTtoLEQProofCompilable.SC.CC.compile_aexp in *; simpl in *.
        invs H. invs H2. invs H7. invs H1. invs H9. invs H13. invs H15. invs H17.
        invs H19. unfold exp_invariant_prop in H10. simpl in H10. destruct H10.
        invs H5. invs H22. invs H8. invs H23. invs H27. 
        assert (n2 = 0).
        symmetry in H29. 
        eapply leb_iff_conv in H29.
        lia.  
        econstructor. econstructor; try eassumption.
        unfold exp_postcondition_prop.
        assert (val1 = n2).
        pose proof aexp_stack_sem_det TARGET.fenv stk' (Var_Stk 2) (stk', n2) (stk', val1) H28 H14.
        invs H20; reflexivity.
        rewrite H20. rewrite H0.
        assert (val = (val - 0)) by lia.
        rewrite <- H21. reflexivity.
        repeat econstructor.
  Defined.
    
End CompileExpTreeOnly.
  

