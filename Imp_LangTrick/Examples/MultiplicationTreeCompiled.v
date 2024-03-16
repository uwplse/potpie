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

End CompileProdTreeOnly.
