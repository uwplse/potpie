From Coq Require Import String List Arith.
From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage StackLogic Imp_LangLogHoare HoareTree StkHoareTree.
From Imp_LangTrick Require Import ProofCompilableCodeCompiler.
From Imp_LangTrick.Imp Require Import Imp_LangLogProp Imp_LangLogSubst ImpVarMap Imp_LangImpHigherOrderRel Imp_LangLogPropDec.
From Imp_LangTrick Require Import FunctionWellFormed ParamsWellFormed.
From Imp_LangTrick.SpecCompiler Require Import TranslationPure FactEnvTranslator.
From Imp_LangTrick.ProofCompiler Require Import ProofCompilerHelpers. 
From Imp_LangTrick.Stack Require Import StateUpdateAdequacy. 

Module Type TreeProofCompilerType.
  Parameter tree_proof_compiler : nat -> list ident -> imp_hoare_tree -> stk_hoare_tree.
End TreeProofCompilerType.
                                                                      

Module TreeProofCompiler (CC: CodeCompilerType) (SC: SpecificationCompilerType) <: TreeProofCompilerType.
  Fixpoint tree_proof_compiler (args: nat) (idents: list ident) (tree: imp_hoare_tree) : stk_hoare_tree :=
    let sc := SC.comp_logic args idents in
    let cc := (fun i => CC.compile_imp i idents args) in
    let ac := (fun a => CC.compile_aexp a idents args) in
    let bc := (fun b => CC.compile_bexp b idents args) in
    let vc := CC.idents_to_map idents in
    let tpc := tree_proof_compiler args idents in
    let implc := (fun p => match p with
                        | (p1, p2) => (sc p1, sc p2)
                        end) in
    match tree with
    | ImpHTSkip P => StkHTSkip (sc P)
    | ImpHTAssign P x a =>
        StkHTAssign (sc P) (vc x) (ac a)
    | ImpHTSeq P Q R i1 i2 H1 H2 =>
        StkHTSeq (sc P) (sc R) (sc Q) (cc i1) (cc i2)
                 (tpc H1) (tpc H2)
    | ImpHTIf P Q b i1 i2 H1 H2 =>
        let P' := sc P in
        let Q' := sc Q in
        let b' := bc b in
        let i1' := cc i1 in
        let i2' := cc i2 in
        StkHTIf P' Q' b' i1' i2'
                (StkHTCon (atruestk b' P', sc (atrueImp_Lang b P))
                          (Q', Q')
                          i1'
                          (tpc H1))
                (StkHTCon (afalsestk b' P', sc (afalseImp_Lang b P))
                          (Q', Q')
                          i2'
                          (tpc H2))
    | ImpHTWhile P b i H =>
        StkHTCon (sc P, sc P)
                 (afalsestk (bc b) (sc P), sc (afalseImp_Lang b P))
                 (cc (WHILE_Imp_Lang b i))
                 (StkHTWhile (sc P) (bc b) (cc i)
                             (StkHTCon (atruestk (bc b) (sc P), sc (atrueImp_Lang b P))
                                       (sc P, sc P)
                                       (cc i)
                                       (tpc H)))
    | ImpHTConLeft Impl i Q n H =>
        StkHTConLeft (implc Impl) (cc i) (sc Q) n (tpc H)
    | ImpHTConRight P i Impl n H =>
        StkHTConRight (sc P) (cc i) (implc Impl) n (tpc H)
    end.
End TreeProofCompiler.

Module TreeProofCompilerSound (PC: ProofCompilableType).
  Module TPC := TreeProofCompiler(PC.CC) (PC.SC).
  Module SC := PC.SC.
  Module CC := PC.CC.
  Include TPC.
    
Lemma tree_compiler_sound :
      forall (d1 d2: AbsEnv) (i: imp_Imp_Lang) (fenv: fun_env)
        (facts: implication_env)
        (fact_cert: Imp_LangLogHoare.fact_env_valid facts fenv)
        facts'
        (hl: hl_Imp_Lang d1 i d2 facts fenv),
      forall (funcs: list fun_Imp_Lang),
        fenv_well_formed' funcs fenv ->
        forall (map: list ident) (args : nat)
          (s1: AbsState) (i': imp_stack)
          (s2: AbsState) (fenv': fun_env_stk),
        forall (OKfuncs: funcs_okay_too funcs fenv')
          (OKparams : Forall (fun func => all_params_ok (Imp_LangTrickLanguage.Args func) (Imp_LangTrickLanguage.Body func)) funcs),
          fun_app_imp_well_formed fenv funcs i ->
          aimp_always_wf funcs map args d1 i d2 fenv facts hl ->
          PC.check_proof fenv funcs d1 d2 i facts map args hl ->
          SC.comp_logic args map d1 = s1 ->
          SC.comp_logic args map d2 = s2 ->
          SC.check_logic d1 = true ->
          SC.check_logic d2 = true ->
          i' = CC.compile_imp i map args ->
          CC.check_imp i = true ->
          AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) d1 ->
          AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map) d2 ->
          imp_rec_rel (var_map_wf_wrt_imp map) i ->
          PC.valid_imp_trans_def facts facts' fenv fenv' map args ->
          stk_valid_tree s1 i' s2 fenv' facts'
          (tree_proof_compiler args map (imp_tree_constructor d1 i d2  fenv facts hl)).
Proof. 
    induction hl; intros; simpl in *; subst. 
    - econstructor; try reflexivity. inversion H2; subst; try discriminate; try eassumption. 
    eapply PC.skip_compilation_okay; eassumption.
    unfold PC.valid_imp_trans_def in H12. eapply H12.  
    - econstructor; try reflexivity; inversion H2; subst; try discriminate; invs Hi.
      invs_aimpwf_helper H1; try discriminate. invs H11. invs H30. destruct H29.
      invs H29.  
      assert (imp_has_variable x (ASSIGN_Imp_Lang x a)).
      econstructor. eapply String.eqb_eq. reflexivity.  
      specialize (H31 x H32).
      specialize (H19 (SC.comp_logic args map P) (CC.idents_to_map map x) eq_refl H35 H31 eq_refl).
      rewrite H19. 
      pose proof StackUpdateAdequacy.state_update_adequacy_forwards.
      invs H2; try discriminate; invs Hi0.  
      eapply H33; try reflexivity; try eassumption. 

      + eapply PC.assign_compilation_commutes. inversion H2; subst; try discriminate; try eassumption.
      + eapply H12.
      + eapply H18; try eassumption.
        * invs H0. eassumption.
        * invs_aimpwf_helper H1; try discriminate. eassumption.
        * invs H11. invs H22. destruct H21. invs H21. eassumption.      
    - pose proof StkValidHTSeq (SC.comp_logic args map P) (CC.compile_imp (SEQ_Imp_Lang i1 i2) map args) (SC.comp_logic args map Q) fenv' facts' (SC.comp_logic args map R) 
    (tree_proof_compiler args map
    (imp_tree_constructor P i1 R fenv fact_env hl1))
    (tree_proof_compiler args map
        (imp_tree_constructor R i2 Q fenv fact_env hl2))
    (CC.compile_imp i1 map args)
    (CC.compile_imp i2 map args).
    eapply X. 
      + pose proof PC.sequence_compilation_commutes args map i1 i2. eapply H3. eassumption.
      + eapply H12.
      + eapply IHhl1; try eassumption; try reflexivity. 
        * invs H0. apply H14.
        * invs_aimpwf_helper H1. eapply H15.  
        * invs H2; try discriminate. invs Hi. 
          unfold eq_rect in H3. 
          pose proof UIP_imp_refl (SEQ_Imp_Lang i1 i2) Hi. invs H17. invs H3. 
          inversion_sigma_helper H20. apply H15.    
        * invs H2; try discriminate. invs Hi. unfold eq_rect in H3. 
          pose proof UIP_imp_refl (SEQ_Imp_Lang i1 i2) Hi. invs H17. invs H3. 
          inversion_sigma_helper H20. assumption.
        * invs H2; try discriminate. invs Hi. unfold eq_rect in H3. 
          pose proof UIP_imp_refl (SEQ_Imp_Lang i1 i2) Hi. invs H17. invs H3. 
          inversion_sigma_helper H20. assumption.
        * invs_aimpwf_helper H1. eassumption. 
        * invs_aimpwf_helper H1. invs H4. eassumption.
      + eapply IHhl2; try eassumption; try reflexivity. 
        * invs H0. apply H15.
        * invs_aimpwf_helper H1. eapply H16.  
        * invs H2; try discriminate. invs Hi. 
          unfold eq_rect in H3. 
          pose proof UIP_imp_refl (SEQ_Imp_Lang i1 i2) Hi. invs H17. invs H3. 
          inversion_sigma_helper H21. apply H16.    
        * invs H2; try discriminate. invs Hi. 
          unfold eq_rect in H3. 
          pose proof UIP_imp_refl (SEQ_Imp_Lang i1 i2) Hi. invs H17. invs H3. 
          inversion_sigma_helper H21. eassumption. 
        * invs H2; try discriminate. invs Hi. 
          unfold eq_rect in H3. 
          pose proof UIP_imp_refl (SEQ_Imp_Lang i1 i2) Hi. invs H17. invs H3. 
          inversion_sigma_helper H21. eassumption. 
        * invs_aimpwf_helper H1. eassumption. 
        * invs_aimpwf_helper H1. invs H4. eassumption.
    - eapply StkValidHTIf.
      + eapply PC.if_compilation_commutes; eassumption.
      + invs H12. eapply H4.
      + invs H2; try discriminate. invs Hi. invs H0. 
        eapply H15; try eassumption. invs H11. invs H29. destruct H21.
        invs H21. eassumption.     
      + destruct H12 as (LL& (L & R)). 
        eapply StkValidHTCon. 
        * reflexivity.
        * reflexivity.
        * pose proof PC.size_change_implication_okay (SC.comp_logic args map (P)) (atruestk (CC.compile_bexp b map args) (SC.comp_logic args map P)) b map args fenv P (fun bval : bool => bval = true) fenv' funcs.
          pose proof PC.if_check_implies_condition_then_else_check b i1 i2 H8. 
          destruct H4. 
          pose proof PC.spec_lp_conjunction_check P b (fun bval : bool => bval = true)
          H5 H4. 
          pose proof PC.spec_conjunction_commutes args map P b (fun bval : bool => bval = true) H12 H5 H4.
          unfold atrueImp_Lang.
          rewrite H13.
          rewrite Nat.add_comm. 
          (* unfold atruestk in H3.  *)
          eapply H3; try eassumption; try reflexivity.    
        * unfold aimpstk; intros; try eassumption.
        * eapply IHhl1; try eassumption; try reflexivity. 
          -- invs H0. apply H15.
          -- invs_aimpwf_helper H1. eapply H13.  
          -- invs H2; try discriminate. invs Hi. 
            unfold eq_rect in H3. 
            pose proof UIP_imp_refl (IF_Imp_Lang b i1 i2) Hi. invs H19. invs H3. 
            inversion_sigma_helper H21. apply H17.    
          -- invs H2; try discriminate. invs Hi. 
            unfold eq_rect in H3. 
            pose proof UIP_imp_refl (IF_Imp_Lang b i1 i2) Hi. invs H19. invs H3. 
            inversion_sigma_helper H21. assumption.
          -- invs H2; try discriminate. invs Hi. 
            unfold eq_rect in H3. 
            pose proof UIP_imp_refl (IF_Imp_Lang b i1 i2) Hi. invs H19. invs H3. 
            inversion_sigma_helper H21. assumption.
          -- invs_aimpwf_helper H1. econstructor; try eassumption.
            econstructor. econstructor. econstructor. invs H11. invs H27. destruct H22. invs H22. eassumption. 
          -- invs_aimpwf_helper H1. invs H4. eassumption.
          -- econstructor; try eassumption; try econstructor; try eassumption.   
      + destruct H12 as (LL& (L & R)). 
        eapply StkValidHTCon. 
        * reflexivity.
        * reflexivity.
        * pose proof PC.size_change_implication_okay (SC.comp_logic args map (P)) (afalsestk (CC.compile_bexp b map args) (SC.comp_logic args map P)) b map args fenv P (fun bval : bool => bval = false) fenv' funcs.
          pose proof PC.if_check_implies_condition_then_else_check b i1 i2 H8. 
          destruct H4. 
          pose proof PC.spec_lp_conjunction_check P b (fun bval : bool => bval = false)
          H5 H4. 
          pose proof PC.spec_conjunction_commutes args map P b (fun bval : bool => bval = false) H12 H5 H4.
          unfold afalseImp_Lang.
          rewrite H13.
          rewrite Nat.add_comm. 
          (* unfold atruestk in H3.  *)
          eapply H3; try eassumption; try reflexivity.    
        * unfold aimpstk; intros; try eassumption.
        * eapply IHhl2; try eassumption; try reflexivity. 
          -- invs H0. apply H16.
          -- invs_aimpwf_helper H1. eapply H14.  
          -- invs H2; try discriminate. invs Hi. 
            unfold eq_rect in H3. 
            pose proof UIP_imp_refl (IF_Imp_Lang b i1 i2) Hi. invs H19. invs H3. 
            inversion_sigma_helper H22. apply H18.    
          -- invs H2; try discriminate. invs Hi. 
            unfold eq_rect in H3. 
            pose proof UIP_imp_refl (IF_Imp_Lang b i1 i2) Hi. invs H19. invs H3. 
            inversion_sigma_helper H22. assumption.
          -- invs H2; try discriminate. invs Hi. 
            unfold eq_rect in H3. 
            pose proof UIP_imp_refl (IF_Imp_Lang b i1 i2) Hi. invs H19. invs H3. 
            inversion_sigma_helper H22. assumption.
          -- invs_aimpwf_helper H1. econstructor; try eassumption.
            econstructor. econstructor. econstructor. invs H11. invs H27. destruct H22. invs H22. eassumption. 
          -- invs_aimpwf_helper H1. invs H4. eassumption.
          -- invs_aimpwf_helper H1.
           econstructor; try eassumption; try econstructor; try eassumption.
  - eapply StkValidHTCon; try reflexivity.
    + unfold aimpstk; intros; eassumption. 
    + pose proof PC.size_change_implication_okay (SC.comp_logic args map (P)) (afalsestk (CC.compile_bexp b map args) (SC.comp_logic args map P)) b map args fenv P (fun bval : bool => bval = false) fenv' funcs.
      pose proof PC.while_check_implies_condition_loop_check b i H8. 
      destruct H4. 
      pose proof PC.spec_lp_conjunction_check P b (fun bval : bool => bval = false)
      H5 H4. 
      pose proof PC.spec_conjunction_commutes args map P b (fun bval : bool => bval = false) H13 H5 H4.
      unfold afalseImp_Lang.
      rewrite H14.
      rewrite Nat.add_comm. 
      (* unfold atruestk in H3.  *)
      eapply H3; try eassumption; try reflexivity.
    + eapply StkValidHTWhile; try reflexivity. 
      * eapply PC.while_compilation_commutes; eassumption.
      * destruct H12. destruct H4. eassumption.
      * invs H2; try discriminate. invs HeqP. invs Hi. invs H0. eapply H14; try eassumption. 
        invs H10. invs H25. invs H21. invs H26. eassumption.         
      * eapply StkValidHTCon; try reflexivity.
        --pose proof PC.size_change_implication_okay (SC.comp_logic args map (P)) (atruestk (CC.compile_bexp b map args) (SC.comp_logic args map P)) b map args fenv P (fun bval : bool => bval = true) fenv' funcs.
          pose proof PC.while_check_implies_condition_loop_check b i H8. 
          destruct H4. 
          pose proof PC.spec_lp_conjunction_check P b (fun bval : bool => bval = true)
          H5 H4. 
          pose proof PC.spec_conjunction_commutes args map P b (fun bval : bool => bval = true) H13 H5 H4.
          unfold atrueImp_Lang.
          rewrite H14.
          rewrite Nat.add_comm. 
          (* unfold atruestk in H3.  *)
          eapply H3; try eassumption; try reflexivity.
        --unfold aimpstk; intros; eassumption.
        -- eapply IHhl; try reflexivity; try eassumption.
          ++invs H0; eassumption.
          ++invs_aimpwf_helper H1. eapply H13.
          ++invs H2; try discriminate. invs HeqP. invs Hi. unfold eq_rect in H3.
          pose proof UIP_imp_refl (WHILE_Imp_Lang b i) Hi. invs H18.
          pose proof UIP_AbsEnv_refl (afalseImp_Lang b P) HeqP. invs H18. invs H3.  
          inversion_sigma_helper H21. assumption.
          ++invs H2; try discriminate. invs HeqP. invs Hi. eassumption.
          ++invs H2; try discriminate. invs HeqP. invs Hi. eassumption.
          ++econstructor; try eassumption. econstructor. econstructor. econstructor.
            invs H11. invs H14. destruct H4. invs H4. apply H19.
          ++invs H11. eassumption.
  - eapply StkValidHTConLeft; try reflexivity; try eassumption.
    + destruct H12. apply H4.
    + invs H2; try discriminate. invs H3. inversion_sigma_helper H19. 
      destruct H12. destruct H16. 
      specialize (H16 n0 P' P0 (SC.comp_logic args map P') (SC.comp_logic args map P0)
      H5 H7 eq_refl eq_refl nth). 
      unfold StackLogic.fact_env_valid in H17. 
      eapply H17. eapply nth_error_In. apply H16.
    + invs H2; try discriminate. invs H3. inversion_sigma_helper H19. 
      destruct H12. destruct H16. 
      specialize (H16 n0 P' P0 (SC.comp_logic args map P') (SC.comp_logic args map P0)
      H5 H7 eq_refl eq_refl nth). eassumption.
    + eapply IHhl; try eassumption; try reflexivity.
      * invs_aimpwf_helper H1; try discriminate. inversion_sigma_helper H28. eassumption.
      * invs H2; try discriminate. invs H3. inversion_sigma_helper H19. eassumption.
      * invs H2; try discriminate. invs H3. inversion_sigma_helper H19. eassumption.
      * invs_aimpwf_helper H1; try discriminate. inversion_sigma_helper H28. eassumption.
  - eapply StkValidHTConRight; try reflexivity; try eassumption.
    + destruct H12. apply H4.
    + invs H2; try discriminate. invs H3. inversion_sigma_helper H19. 
      destruct H12. destruct H16. 
      specialize (H16 n0 Q0 Q' (SC.comp_logic args map Q0) (SC.comp_logic args map Q')
      H7 H14 eq_refl eq_refl nth). 
      unfold StackLogic.fact_env_valid in H17. 
      eapply H17. eapply nth_error_In. apply H16.
    + invs H2; try discriminate. invs H3. inversion_sigma_helper H19. 
      destruct H12. destruct H16. 
      specialize (H16 n0 Q0 Q' (SC.comp_logic args map Q0) (SC.comp_logic args map Q')
      H7 H14 eq_refl eq_refl nth). eassumption.
    + eapply IHhl; try eassumption; try reflexivity.
      * invs_aimpwf_helper H1; try discriminate. inversion_sigma_helper H28. eassumption.
      * invs H2; try discriminate. invs H3. inversion_sigma_helper H19. eassumption.
      * invs H2; try discriminate. invs H3. inversion_sigma_helper H19. eassumption.
      * invs_aimpwf_helper H1; try discriminate. inversion_sigma_helper H28. eassumption.
Qed. 
                 
End TreeProofCompilerSound.
