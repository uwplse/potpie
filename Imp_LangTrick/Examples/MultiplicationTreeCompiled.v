From Coq Require Import Psatz Arith String List.

From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang SeriesExample FunctionWellFormed EnvToStackLTtoLEQ TranslationPure ProofCompMod StackLangTheorems ParamsWellFormed Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems Imp_LangDec Imp_LangLogPropDec UIPList StackLanguage.

Local Open Scope list_scope.
Local Open Scope string_scope.
From Imp_LangTrick Require Import ProofCompAutoAnother BloomFilterArrayProgram.
From Imp_LangTrick Require Import LogicProp Imp_LangLogProp Imp_LangLogHoare  ProofCompAuto ProofCompCodeCompAgnosticMod AimpWfAndCheckProofAuto StackLangTheorems.


From Imp_LangTrick Require Import Multiplication HelperFenvWF.
Local Open Scope imp_langtrick_scope.

Definition prod_comp_map := "y" :: "x" :: nil. 

Module SourceProd <: SourceProgramType.
  Definition program := prod_body.
  Definition precond := true_precondition.
  Definition postcond := prod_postcondition.
  Definition fenv := series_fenv.
  Definition facts := prod_facts. 
  Definition hoare_triple := (partial_prod_correct series_fenv).
  Definition idents := prod_comp_map.
  Definition num_args := 2.
  Definition funcs := (prod_function :: exp_function :: fraction_addition_denominator_fun :: fraction_addition_numerator_fun :: fraction_subtraction_numerator_fun ::
                                     (init_fenv "id") :: nil).
End SourceProd.


Module TargetProd <: TargetProgramType. 
  Module CAPC := LTtoLEQCompilerAgnostic.
  Module SP := SourceProd.
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
End TargetProd.

Module CompileProdTreeOnly.
  Module CAPC := LTtoLEQCompilerAgnostic.
  Module SOURCE := SourceProd.
  Module TARGET := TargetProd.

  Ltac unfold_src_tar := unfold SOURCE.idents, SOURCE.precond, SOURCE.program, SOURCE.postcond, SOURCE.fenv, SOURCE.hoare_triple, SOURCE.num_args, SOURCE.funcs, TARGET.precond, TARGET.postcond, TARGET.program, TARGET.compile_imp_lang_log, TARGET.fenv in *.

  Ltac unfold_idents := unfold SOURCE.idents in *; unfold prod_comp_map in *.

  

  Lemma stack_valid_facts :
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
      unfold product_invariant_prop. simpl. split; lia.
      repeat econstructor.
    + invs H.
      * invs H0. unfold LTtoLEQProofCompilable.SC.CC.compile_aexp in *. simpl in *. clear H.
        econstructor. invs H. inv H3. 
        econstructor. invs H. invs H3. invs H8. invs H2. invs H10. 
        invs H14. invs H16. invs H18.  
        econstructor; try eassumption. 
        unfold product_invariant_prop in H11. simpl in H11. 
        unfold prod_postcondition_prop. destruct H11.
        invs H6. invs H23. invs H9. invs H24. invs H28. 
        symmetry in H30. 
        rewrite leb_iff_conv in H30. 
        assert (n2 = 0) by lia. rewrite H1 in *.  
        assert ((stk', 0) = (stk', val1)).
        eapply aexp_stack_sem_det; try eassumption.
        invs H21.   
        lia. 
        repeat econstructor.
      * clear H. invs H0. invs H. clear H0 H. econstructor.
        invs H. invs H2. apply H3. 
        invs H. invs H2. invs H7. invs H1. invs H9. invs H13. invs H15. invs H17.
        econstructor. econstructor.
        econstructor. eassumption. 
        econstructor. eassumption.
        econstructor. econstructor. simpl. eassumption.
        econstructor. econstructor. econstructor.
        simpl. eassumption.
        simpl. eassumption.
        econstructor. unfold product_invariant_prop. simpl.
        invs H5. invs H21. invs H6. invs H23. 
        (* invs H26.  *)
        symmetry in H29.
        apply leb_complete in H29. 
        unfold LTtoLEQProofCompilable.SC.CC.compile_aexp in *.
        simpl in *.
        assert (stk' = stk).
        invs H27; reflexivity. rewrite H0 in *. 
        assert ((stk, n2) = (stk, val1)).
        eapply aexp_stack_sem_det; try eassumption. 
        invs H20. 
        (* invs H30. *)
        unfold product_invariant_prop in H10. simpl in H10. 
        destruct H10.
        split; try lia.
        invs H27. 
        assert ((val - (val1 - 1)) = 1 + (val - val1)) by lia.
        rewrite H0. unfold Nat.add at 2. simpl. lia. 
        repeat econstructor.
        contradiction.  
  Qed.
End CompileProdTreeOnly.
