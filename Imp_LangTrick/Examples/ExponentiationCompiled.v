From Coq Require Import Psatz Arith String List.

From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang SeriesExample FunctionWellFormed EnvToStackLTtoLEQ TranslationPure ProofCompMod StackLangTheorems ParamsWellFormed Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems Imp_LangDec Imp_LangLogPropDec UIPList StackLanguage.

Local Open Scope list_scope.
Local Open Scope string_scope.
From Imp_LangTrick Require Import ProofCompAutoAnother BloomFilterArrayProgram.
From Imp_LangTrick Require Import LogicProp Imp_LangLogProp Imp_LangLogHoare  ProofCompAuto ProofCompCodeCompAgnosticMod AimpWfAndCheckProofAuto StackLangTheorems Multiplication MultiplicationTreeCompiled HelperFenvWF MultiplicationCompiled.
Local Open Scope imp_langtrick_scope.

From Imp_LangTrick Require Export ExponentiationTreeCompiled.

Module CompileExp <: ProgramProofCompilationType.
  Include CompileExpTreeOnly.

  Lemma fact_cert : Imp_LangLogHoare.fact_env_valid SOURCE.facts SOURCE.fenv.
  Proof.
    unfold SOURCE.facts. unfold SOURCE.fenv.
    apply exp_fact_env_valid. reflexivity. 
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
    unfold_src_tar. unfold exp_body. unfold exp_loop. econstructor. repeat econstructor.
    econstructor. repeat econstructor.
    econstructor. econstructor. econstructor.
    repeat econstructor. reflexivity. 
    simpl. left. reflexivity.
    reflexivity.
    econstructor. apply ImpVarMap.ImpHasVarSeq__right. simpl. repeat econstructor.
    left. reflexivity.
    repeat econstructor.                 
  Defined.


  Lemma exp_invariant_wf_proof :
    ProofCompilerBase.AbsEnv_prop_wf SOURCE.idents exp_invariant.
  Proof.
    unfold_idents. AbsEnv_prop_wf_helper; deal_with_var_map_wf.
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
  - eapply exp_stack_facts_valid.
  Qed. 
                                     

  Lemma aimp_always_wf_proof : ProofCompilerHelpers.aimp_always_wf SOURCE.funcs SOURCE.idents SOURCE.num_args SOURCE.precond SOURCE.program SOURCE.postcond SOURCE.fenv SOURCE.facts SOURCE.hoare_triple.
  Proof.
  unfold ProofCompilerHelpers.aimp_always_wf. unfold SOURCE.hoare_triple.
  unfold partial_exp_correct. simpl.
  unfold SOURCE.program. unfold exp_body.
  unfold_idents.
  hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases; [ | | | repeat econstructor .. ].
                                                                    
  - symmetry. eassumption.
  - hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases; [ | | | repeat econstructor .. ].
    + symmetry. eassumption.
    + unfold_idents; hl_Imp_Lang_wf_roc_pre_helper; simplify_var_map_wf_cases; [ | | | repeat econstructor .. ].
      * simpl. pose proof ((exp_fact_env_valid series_fenv eq_refl true_precondition
      (AbsEnvLP
      (Imp_Lang_lp_arith
         (NaryProp nat aexp_Imp_Lang exp_invariant_prop
            (PARAM_Imp_Lang 0
             :: PARAM_Imp_Lang 1
                :: PARAM_Imp_Lang 0 :: CONST_Imp_Lang 1 :: nil))))
      (or_introl eq_refl))). eassumption.
      * f_equal. rewrite UIP_option_refl. reflexivity.
      * hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; repeat econstructor.
    + hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases; repeat econstructor.
  - unfold_idents.
    hl_Imp_Lang_wf_roc_post_helper; simplify_var_map_wf_cases;
      [ | repeat econstructor .. ].
    unfold exp_loop.
    hl_imp_lang_wf_while_helper; simplify_var_map_wf_cases; [ | repeat econstructor .. ].
    hl_Imp_Lang_wf_seq_helper; simplify_var_map_wf_cases.
    -- right. assumption.
    -- hl_Imp_Lang_wf_roc_pre_helper; simplify_var_map_wf_cases.
       ++ simpl. eapply (exp_fact_env_valid series_fenv eq_refl
       (atrueImp_Lang (CONST_Imp_Lang 1 <=d VAR_Imp_Lang "x") exp_invariant)
  (AbsEnvLP
     (Imp_Lang_lp_arith
        (NaryProp nat aexp_Imp_Lang exp_invariant_prop
           (PARAM_Imp_Lang 0
            :: PARAM_Imp_Lang 1
               :: (VAR_Imp_Lang "x" -d CONST_Imp_Lang 1)
                  :: ("mult" @d
                      VAR_Imp_Lang "y" :: PARAM_Imp_Lang 1 :: nil) :: nil))))). 
        right. left. reflexivity. 
       ++ rewrite UIP_option_refl. reflexivity.
       ++ right. assumption.
       ++ destruct H; [ |invs H]. left. assumption.
       ++ right. assumption.
       ++ hl_imp_lang_wf_assign_helper; simplify_var_map_wf_cases.
          ** right; assumption.
          ** repeat econstructor.
          ** right; assumption.
          ** repeat econstructor.
          ** econstructor. repeat econstructor.
             exists. simpl. left. reflexivity.
             simpl. reflexivity.
             simpl. unfold prod_body.
             econstructor. apply ImpVarMap.ImpHasVarSeq__right. repeat econstructor.
             left. reflexivity.   
       ++ simpl. econstructor. econstructor. econstructor. econstructor.
       repeat econstructor.
       econstructor. repeat econstructor.
       econstructor. repeat econstructor.
       econstructor. econstructor. repeat econstructor.
       exists. simpl. left. reflexivity.
       reflexivity.
       simpl. unfold prod_body.
       econstructor. apply ImpVarMap.ImpHasVarSeq__right. 
       repeat econstructor.
       left. reflexivity.
       econstructor. 
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
    unfold partial_exp_correct. unfold exp_body. unfold exp_loop.
    unfold_idents.
    check_proof_helper.
    repeat econstructor.
    repeat econstructor.
    unfold funcs_okay_too in OK. destruct OK. invs H.
    destruct H3. eassumption.  
    unfold funcs_okay_too in OK. destruct OK. invs H.
    destruct H3. eassumption.
    repeat econstructor. 
    unfold funcs_okay_too in OK. destruct OK. invs H.
    destruct H3. invs H4. invs H7. 
    eapply StackPurestBase.aexp_frame_implies_aexp_pure. destruct H8. eassumption.  
  Qed.

  Lemma translate_precond_proof :
    CAPC.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.precond = TARGET.precond.
  Proof.
    simpl. reflexivity.
  Defined.

  Lemma translate_postcond_proof :
    CAPC.SC.comp_logic SOURCE.num_args SOURCE.idents SOURCE.postcond = TARGET.postcond.
  Proof.
    simpl. unfold TARGET.postcond. simpl. reflexivity.
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
  
  
End CompileExp.

Module CompiledExpProof := CompileProof(CompileExp). 