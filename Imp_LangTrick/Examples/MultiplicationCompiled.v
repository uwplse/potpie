From Coq Require Import Psatz Arith String List.

From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang SeriesExample FunctionWellFormed EnvToStackLTtoLEQ TranslationPure ProofCompMod StackLangTheorems ParamsWellFormed Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems Imp_LangDec Imp_LangLogPropDec UIPList StackLanguage.

Local Open Scope list_scope.
Local Open Scope string_scope.
From Imp_LangTrick Require Import ProofCompAutoAnother BloomFilterArrayProgram.
From Imp_LangTrick Require Import LogicProp Imp_LangLogProp Imp_LangLogHoare  ProofCompAuto ProofCompCodeCompAgnosticMod AimpWfAndCheckProofAuto StackLangTheorems.


From Imp_LangTrick Require Import Multiplication HelperFenvWF.
Local Open Scope imp_langtrick_scope.
From Imp_LangTrick Require Export MultiplicationTreeCompiled.


Module CompileProd <: ProgramProofCompilationType.
  Include CompileProdTreeOnly.
 


  Lemma fact_cert : Imp_LangLogHoare.fact_env_valid SOURCE.facts SOURCE.fenv.
  Proof.
    unfold SOURCE.facts. unfold SOURCE.fenv.
    apply prod_fact_env_valid.
  Defined.
  
  Lemma fenv_well_formed_proof : fenv_well_formed' SOURCE.funcs SOURCE.fenv.
  Proof.
    apply big_fenv_well_formed. 
  Defined.
      
  Lemma funcs_okay_too_proof : funcs_okay_too SOURCE.funcs TARGET.fenv.
  Proof.
    apply big_funcs_okay_too.
  Defined.


  Lemma all_params_ok_for_funcs_proof : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func)
                                                                                                                                                  (Imp_LangTrickLanguage.Body func))
                                               SOURCE.funcs.
  Proof.
    unfold SOURCE.funcs.
    unfold prod_function, exp_function, fraction_addition_denominator_fun, fraction_addition_numerator_fun, init_fenv. repeat econstructor.
  Defined.

Lemma imp_code_wf_proof : imp_rec_rel (var_map_wf_wrt_imp SOURCE.idents) SOURCE.program.
  Proof.
    unfold_idents. deal_with_var_map_wf.
    symmetry.  assumption.
  Defined.

  Lemma PARAM0_wf :
    var_map_wf_wrt_aexp SOURCE.idents (PARAM_Imp_Lang 0). 
  Proof.
    unfold_idents. deal_with_var_map_wf.
  Qed.        

  Lemma PARAM1_wf :
    var_map_wf_wrt_aexp SOURCE.idents (PARAM_Imp_Lang 1). 
  Proof.
    unfold_idents. deal_with_var_map_wf.
  Qed.

  

  Lemma VARx_wf :
    var_map_wf_wrt_aexp SOURCE.idents (VAR_Imp_Lang "x").
  Proof.
    unfold_idents. deal_with_var_map_wf.
  Qed.
  
  Lemma VARy_wf :
    var_map_wf_wrt_aexp SOURCE.idents (VAR_Imp_Lang "y").
  Proof.
    unfold_idents. deal_with_var_map_wf.
  Qed.        

  Lemma CONST0_wf : 
    var_map_wf_wrt_aexp SOURCE.idents (CONST_Imp_Lang 0). 
  Proof.
    unfold_idents. deal_with_var_map_wf.
  Qed. 

  Lemma VARxMINUS1_wf :
    var_map_wf_wrt_aexp SOURCE.idents
    (VAR_Imp_Lang "x" -d CONST_Imp_Lang 1). 
  Proof.
    unfold_idents. deal_with_var_map_wf. intros.
    match goal with
    | [ H: In _ ?a |- _ ] =>
        remember a as b eqn:Hb; simpl in Hb; subst b
    end.
    finite_in_implication.
  Qed.               

  Lemma precond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.precond.
  Proof.
    unfold_idents; AbsEnv_prop_wf_helper; deal_with_var_map_wf.
  Qed.   

  Lemma postcond_wf_proof : AbsEnv_prop_rel (var_map_wf_wrt_aexp SOURCE.idents) (var_map_wf_wrt_bexp SOURCE.idents) SOURCE.postcond.
  Proof.
    unfold_idents; AbsEnv_prop_wf_helper; deal_with_var_map_wf.
  Qed.

  

  Lemma VARyPLUSPARAM1_wf' : 
    imp_rec_rel (var_map_wf_wrt_imp SOURCE.idents)
    ("y" <- (VAR_Imp_Lang "y" +d PARAM_Imp_Lang 1)). 
  Proof.
    unfold_idents.
    deal_with_var_map_wf.
  Qed.  

  Lemma VARyPLUSPARAM1_wf:  
    var_map_wf_wrt_aexp SOURCE.idents
    (VAR_Imp_Lang "y" +d PARAM_Imp_Lang 1). 
  Proof.
    unfold_idents. deal_with_var_map_wf.
    intros. match goal with
            | [ H: In _ ?a |- _ ] =>
                remember a as b eqn:Hb; simpl in Hb; subst b
            end.
    finite_in_implication.
  Qed.        

  Lemma fun_app_well_formed_proof :
    fun_app_imp_well_formed SOURCE.fenv SOURCE.funcs SOURCE.program.
  Proof.
    unfold_src_tar. unfold prod_body. unfold prod_loop. repeat econstructor. 
  Defined.


  Lemma product_invariant_wf_proof :
    ProofCompilerBase.AbsEnv_prop_wf SOURCE.idents product_invariant.
  Proof.
    unfold_idents. AbsEnv_prop_wf_helper; deal_with_var_map_wf.
  Qed.
                                     

  Lemma aimp_always_wf_proof : ProofCompilerHelpers.aimp_always_wf SOURCE.funcs SOURCE.idents SOURCE.num_args SOURCE.precond SOURCE.program SOURCE.postcond SOURCE.fenv SOURCE.facts SOURCE.hoare_triple.
  Proof.
  unfold ProofCompilerHelpers.aimp_always_wf. unfold SOURCE.hoare_triple.
  unfold partial_prod_correct. simpl.
  unfold SOURCE.program. unfold prod_body.
  unfold_idents.
  hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases; [ | | | repeat econstructor .. ].
                                                                    
  - symmetry. eassumption.
  - hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases; [ | | | repeat econstructor .. ].
    + symmetry. eassumption.
    + unfold_idents; hl_Imp_Lang_wf_roc_pre_helper; simplify_var_map_wf_cases; [ | | | repeat econstructor .. ].
      * simpl. pose proof ((prod_fact_env_valid series_fenv true_precondition
      (AbsEnvLP
         (Imp_Lang_lp_arith
            (NaryProp nat aexp_Imp_Lang product_invariant_prop
               (PARAM_Imp_Lang 0
                :: PARAM_Imp_Lang 1
                   :: PARAM_Imp_Lang 0 :: CONST_Imp_Lang 0 :: nil))))
      (or_introl eq_refl))). eassumption.
      * f_equal. rewrite UIP_option_refl. reflexivity.
      * hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; repeat econstructor.
    + hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; repeat econstructor.
  - unfold_idents.
    hl_Imp_Lang_wf_roc_post_helper; simplify_var_map_wf_cases;
      [ | repeat econstructor .. ].
                                                                      
    unfold prod_loop.
    hl_imp_lang_wf_while_helper; simplify_var_map_wf_cases; [ | repeat econstructor .. ].
    hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases.
    -- right. assumption.
    -- hl_Imp_Lang_wf_roc_pre_helper; simplify_var_map_wf_cases.
       ++ simpl. 
          eapply ((prod_fact_env_valid series_fenv)
       (atrueImp_Lang (CONST_Imp_Lang 1 <=d VAR_Imp_Lang "x") product_invariant)
       (AbsEnvLP
          (Imp_Lang_lp_arith
             (NaryProp nat aexp_Imp_Lang product_invariant_prop
                (PARAM_Imp_Lang 0
                 :: PARAM_Imp_Lang 1
                    :: (VAR_Imp_Lang "x" -d CONST_Imp_Lang 1)
                       :: (VAR_Imp_Lang "y" +d PARAM_Imp_Lang 1) :: nil))))).
          right. right. left. reflexivity. 
       ++ rewrite UIP_option_refl. reflexivity.
       ++ right. assumption.
       ++ destruct H; [ |invs H]. left. assumption.
       ++ right. assumption.
       ++ hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases.
          invs H. right. left. reflexivity.
          invs H0.
          repeat econstructor.   
          invs H. right. left. reflexivity.
          invs H0.
          repeat econstructor. 
       ++ simpl. repeat econstructor.
       ++ repeat econstructor.
       ++ repeat econstructor.
       ++ right. assumption.
       ++ destruct H; [ |invs H ]; left; assumption.
       ++ right. assumption.
       ++ repeat econstructor.
       ++ repeat econstructor.
       ++ repeat econstructor.
    -- hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; repeat econstructor.
    -- repeat econstructor.
    -- repeat econstructor.
    -- repeat econstructor.
    -- right. assumption.
    -- repeat econstructor.
    -- repeat econstructor.
    -- repeat econstructor.
  Qed.     

  Ltac check_proof_helper :=
    match goal with
    | [ |- CAPC.PC.check_proof
            _ _ _ _ (SEQ_Imp_Lang _ _) _ _ _
            (hl_Imp_Lang_seq _ _ _ _ _ _ _ _ _ ) ] =>
        CAPC.PC.check_seq;
        try reflexivity;
        try check_proof_helper
    | [ |- CAPC.PC.check_proof
            _ _ _ _ (ASSIGN_Imp_Lang _ _) _ _ _
            (hl_Imp_Lang_assign _ _ _ _ _) ] =>
        CAPC.PC.check_proof_assign_setup;
        try reflexivity;
        try check_proof_helper
    | [ |- CAPC.PC.check_proof
            _ _ _ _ (WHILE_Imp_Lang _ _) _ _ _
            (hl_Imp_Lang_while _ _ _ _ _ _) ] =>
        CAPC.PC.check_proof_while;
        try reflexivity;
        try check_proof_helper
    | [ |- CAPC.PC.check_proof
            _ _ _ _ ?i _ _ _
            (hl_Imp_Lang_consequence_pre _ _ _ _ _ _ _ _ _ _) ] =>
        CAPC.PC.check_hl_pre;
        try reflexivity;
        try check_proof_helper
    | [ |- CAPC.PC.check_proof
            _ _ _ _ ?i _ _ _
            (hl_Imp_Lang_consequence_post _ _ _ _ _ _ _ _ _ _) ] =>
        CAPC.PC.check_hl_post;
        try reflexivity;
        try check_proof_helper
    | [ |- StackUpdateAdequacy.stack_large_enough_for_state ?n _ ] =>
        repeat econstructor
    | [ |- forall fenv',
          fenv_well_formed'
            ?funcs ?fenv ->
          fun_app_well_formed ?fenv
                              ?funcs
                              ?aexp ->
          all_params_ok_aexp ?args ?aexp ->
          var_map_wf_wrt_aexp ?idents ?aexp ->
          funcs_okay_too
            ?funcs
            fenv' ->
          StackPurestBase.aexp_stack_pure_rel
            (CAPC.PC.CC.compile_aexp ?aexp ?idents ?args)
            fenv' ] =>
        intros fenv' FENV_WF FUN_APP ALL_PARAMS WF OK;
        match aexp with
        | APP_Imp_Lang ?f ?args =>
            econstructor; try reflexivity
        | _ =>
            repeat econstructor (* this isn't exactly right -- should stop if it finds function application *)
        end
    | [ |- forall fenv',
          fenv_well_formed'
            ?funcs ?fenv ->
          fun_app_bexp_well_formed ?fenv ?funcs ?bexp ->
          var_map_wf_wrt_bexp ?idents ?bexp ->
          funcs_okay_too
            ?funcs fenv' ->
          StackPurestBase.bexp_stack_pure_rel
            (CAPC.PC.CC.compile_bexp ?bexp ?idents ?args) fenv' ] =>
        intros fenv' FENV_WF FUN_APP WF OK;
        repeat econstructor
    | [ |- forall (s' : StackLogicGrammar.AbsState) (k : nat),
          _ = s' ->
          var_map_wf_wrt_aexp ?idents ?aexp ->
          _ ->
          k = ?num ->
          _ =
            StackLogicBase.state_update
              k
              (CAPC.PC.CC.compile_aexp ?aexp ?idents ?args)
              s' ] =>
        let fs' := fresh "s'" in
        let fk := fresh "k" in
        let Hs' := fresh "Hs'" in
        let WF := fresh "WF" in
        let Hk := fresh "Hk" in
        intros fs' fk Hs' WF _ Hk;
        rewrite <- Hs', Hk; try reflexivity
    | [ |- StackExprWellFormed.aexp_well_formed
            (CAPC.PC.CC.compile_aexp ?aexp ?idents ?args) ] =>
        match aexp with
        | APP_Imp_Lang ?f ?args =>
            econstructor; try reflexivity
        | _ => repeat econstructor
        end
    | [ |- StackExprWellFormed.absstate_well_formed _ ] =>
        repeat econstructor
    end.
  
  Lemma check_proof_proof:
    CAPC.PC.check_proof SOURCE.fenv SOURCE.funcs SOURCE.precond SOURCE.postcond SOURCE.program SOURCE.facts SOURCE.idents SOURCE.num_args SOURCE.hoare_triple.
  Proof.
    unfold_src_tar. unfold SOURCE.facts.
    unfold partial_prod_correct. unfold prod_body. unfold prod_loop.
    unfold_idents.
    check_proof_helper.
  Qed.

  Lemma translate_precond_proof :
    CAPC.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.precond = TARGET.precond.
  Proof.
    simpl. reflexivity.
  Defined.

  Lemma translate_postcond_proof :
    CAPC.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.postcond = TARGET.postcond.
  Proof.
    simpl. reflexivity.
  Defined.

  Lemma check_logic_precond_proof :
    CAPC.SC.check_logic SOURCE.precond = true.
  Proof.
    reflexivity.
  Defined.

  Lemma check_logic_postcond_proof :
    CAPC.SC.check_logic SOURCE.postcond = true.
  Proof.
    simpl. reflexivity.
  Defined.

  Lemma program_compiled_proof : TARGET.program = CAPC.CC.compile_imp SOURCE.program SOURCE.idents SOURCE.num_args.
  Proof.
    simpl. reflexivity.
  Defined.

  Lemma check_imp_proof :
    CAPC.CC.check_imp SOURCE.program = true.
  Proof.
    reflexivity.
  Qed.
  
  Lemma implication_transformer :
    CAPC.PC.valid_imp_trans_def SOURCE.facts TARGET.facts SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
  unfold CAPC.PC.valid_imp_trans_def. split. simpl. lia.
  split. intros. destruct n.
  - simpl in *. rewrite <- H1. rewrite <- H2. 
    invs H3. 
    unfold CAPC.SC.comp_logic. simpl. reflexivity. 
  - destruct n. simpl in *. rewrite <- H1. rewrite <- H2. 
    invs H3. 
    simpl in *. reflexivity. 
    destruct n. simpl in *. rewrite <- H1. rewrite <- H2. 
    invs H3. reflexivity.
    pose proof nth_error_None SOURCE.facts (S (S (S n))).
    destruct H4. simpl in H5. 
    assert (3 <= S (S (S n))) by lia. 
    specialize (H5 H6).
    simpl in H3. rewrite H5 in *. discriminate.
  - unfold StackLogic.fact_env_valid. intros.  
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
End CompileProd.

Module CompiledProdProof := CompileProof(CompileProd). 
