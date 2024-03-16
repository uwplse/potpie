From Coq Require Import String List Arith Psatz.

From Imp_LangTrick Require Import ProofCompiler StackLangTheorems ImpVarMap Imp_LangImpHigherOrderRel ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare Imp_LangImpHigherOrderRelTheorems LogicTranslationBase LogicTranslationAdequate StackLanguage.
From Imp_LangTrick Require Import ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed.
From Imp_LangTrick Require Import TranslationPure Imp_LangTrickLanguage.
From Imp_LangTrick Require Import ProofCompiler FactEnvTranslator.
From Imp_LangTrick Require Import ProofCompMod EnvToStack ProofCompAuto EnvToStackBuggy.
From Imp_LangTrick Require Import TerminatesForSure BuggyProofCompiler ProofCompCodeCompAgnosticMod Multiplication.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(*exp x y = y^x*)
Definition exp_loop : imp_Imp_Lang := WHILE_Imp_Lang (
   (LEQ_Imp_Lang (CONST_Imp_Lang 1) (VAR_Imp_Lang "x")))
   (SEQ_Imp_Lang (ASSIGN_Imp_Lang "y" (APP_Imp_Lang "mult" ((VAR_Imp_Lang "y"):: (PARAM_Imp_Lang 1)::nil))) (ASSIGN_Imp_Lang "x" (MINUS_Imp_Lang (VAR_Imp_Lang "x") (CONST_Imp_Lang 1)))).

Definition exp_body : imp_Imp_Lang := SEQ_Imp_Lang (SEQ_Imp_Lang (ASSIGN_Imp_Lang "x" (PARAM_Imp_Lang 0)) (ASSIGN_Imp_Lang "y" (CONST_Imp_Lang 1))) exp_loop.

Definition exp_function : fun_Imp_Lang :=
   {|Name := "exp"
   ; Args := 2
   ; Ret := "y"
   ; Body := exp_body|}. 


Lemma exp_loop_terminates : 
   forall n dbenv nenv fenv, 
      fenv "mult" = prod_function ->
      AbsEnv_rel true_precondition fenv dbenv nenv -> 
      nenv "x" = n -> 
         exists nenv',
            i_Imp_Lang exp_loop dbenv fenv nenv nenv'.
Proof.
   induction n; intros; invs H0; invs H3; invs H4; unfold exp_loop.
   - econstructor. eapply Imp_Lang_while_done.
      assert ((1 <=? (nenv "x")) = false). 
      eapply leb_iff_conv. lia. rewrite <- H2.    
      econstructor; try rewrite H2; repeat econstructor.      
   -  pose proof prod_terminates (nenv "y" :: v2 :: nil) init_nenv fenv as pnenv.
      assert (AbsEnv_rel true_precondition fenv (nenv "y" :: v2 :: nil) init_nenv) as ptp by (repeat econstructor).
      specialize (pnenv ptp). 
      destruct pnenv as (x, sem). 
      specialize (IHn dbenv (update "x" (update "y" (x "y") nenv "x" - 1) (update "y" (x "y") nenv)) fenv H). 
      assert (AbsEnv_rel true_precondition fenv dbenv
      (update "x" (update "y" (x "y") nenv "x" - 1) (update "y" (x "y") nenv))) as endtp.
      econstructor. econstructor. invs H8. invs H9. econstructor; try econstructor; try eassumption. 
      specialize (IHn endtp). 
      assert (update "x" (update "y" (x "y") nenv "x" - 1) (update "y" (x "y") nenv) "x" = n) as eq. rewrite update_same. rewrite update_other. rewrite H1. lia. unfold not. intros. discriminate.
      specialize (IHn eq). destruct IHn as (estate, esem).
      econstructor. 
      eapply Imp_Lang_while_step. 
      +  assert ((1 <=? (nenv "x")) = true). 
         eapply leb_correct. lia. rewrite <- H2.    
         econstructor; try rewrite H2; repeat econstructor.   
      +  econstructor. econstructor. 
         econstructor; try eassumption. 
         *  simpl; reflexivity.
         *  econstructor. econstructor. exists. econstructor. apply H9.
            econstructor.
         *  simpl. exists.
         *  econstructor. econstructor. econstructor. exists. econstructor.
      +   apply esem.
Qed.     

Lemma exp_terminates : 
   forall dbenv nenv fenv, 
      fenv "mult" = prod_function ->
      AbsEnv_rel true_precondition fenv dbenv nenv -> 
         exists nenv',
            i_Imp_Lang exp_body dbenv fenv nenv nenv'.
Proof.
   intros. invs H0. invs H2. invs H3. invs H7. inv H8. 
   pose proof exp_loop_terminates ((update "y" 1 (update "x" v1 nenv)) "x") dbenv (update "y" 1 (update "x" v1 nenv)) fenv H. 
   assert (AbsEnv_rel true_precondition fenv dbenv (update "y" 1 (update "x" v1 nenv))). econstructor. econstructor. econstructor; econstructor;   eassumption. 
   specialize (H1 H11 eq_refl). destruct H1.
   econstructor. unfold exp_body. econstructor.
   - econstructor. econstructor. apply H7. econstructor. econstructor.
   - apply H1.
Qed.    

Definition exp_postcondition_prop : nat -> nat -> nat -> Prop :=
   fun x => fun y => fun z => y ^ x = z.
   
Definition exp_postcondition := 
   AbsEnvLP (Imp_Lang_lp_arith (TernaryProp nat aexp_Imp_Lang
      exp_postcondition_prop
         (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1) (VAR_Imp_Lang "y"))).

Definition exp_invariant_prop : list nat -> Prop :=
   fun lst => 
   ((List.nth 3 lst 0) = 
   (List.nth 1 lst 0) ^ ((List.nth 0 lst 0) - (List.nth 2 lst 0))) /\ 
      (List.nth 2 lst 0 <= List.nth 0 lst 0).

Definition exp_invariant := 
   AbsEnvLP (Imp_Lang_lp_arith (NaryProp nat aexp_Imp_Lang
      exp_invariant_prop
         ((PARAM_Imp_Lang 0)::(PARAM_Imp_Lang 1)::(VAR_Imp_Lang "x")::(VAR_Imp_Lang "y")::nil))).

Definition exp_facts : implication_env := 
   (true_precondition,
   Imp_LangLogSubst.subst_AbsEnv "x" (PARAM_Imp_Lang 0)
     (Imp_LangLogSubst.subst_AbsEnv "y" (CONST_Imp_Lang 1) exp_invariant))
   ::
   (atrueImp_Lang
   ((LEQ_Imp_Lang (CONST_Imp_Lang 1) (VAR_Imp_Lang "x")))   exp_invariant,
 Imp_LangLogSubst.subst_AbsEnv "y"
   (APP_Imp_Lang "mult" (VAR_Imp_Lang "y" :: PARAM_Imp_Lang 1 :: nil))
   (Imp_LangLogSubst.subst_AbsEnv "x"
      (MINUS_Imp_Lang (VAR_Imp_Lang "x") (CONST_Imp_Lang 1)) exp_invariant))
   ::
   (afalseImp_Lang 
   ((LEQ_Imp_Lang (CONST_Imp_Lang 1) (VAR_Imp_Lang "x")))   exp_invariant,
   exp_postcondition)
   ::
   nil.  

Lemma exp_fact_env_valid : 
   forall fenv, 
   fenv "mult" = prod_function ->
   fact_env_valid exp_facts fenv.
Proof.
   unfold fact_env_valid; intros fenv fenvmult P Q eq. destruct eq. 
   - invs H. simpl. econstructor. econstructor. 
      invs H0. invs H2. invs H3.   
      econstructor. 
      econstructor. apply H7. 
      econstructor. apply H8. 
      econstructor. apply H7. 
      econstructor. econstructor. econstructor.
      unfold exp_invariant_prop. simpl. split; try lia.
      assert (v1 - v1 = 0) by lia. rewrite H1. 
      unfold Nat.pow. lia.
   - destruct H. 
      + invs H. econstructor. invs H0. invs H3. invs H2. 
      invs H4. 
      invs H8. invs H12. invs H14. invs H16. invs H10. invs H11.  
      unfold exp_invariant_prop in H9. simpl in H9.
      assert (AbsEnv_rel true_precondition fenv (val2 :: val0 :: nil) init_nenv). econstructor. econstructor. econstructor; try econstructor; try simpl; try lia; try exists.    
      pose proof prod_terminates (val2 :: val0 :: nil) init_nenv fenv H1.
      destruct H20.
      pose proof partial_prod_correct fenv.
      pose proof Hoare_Imp_Lang_sound true_precondition prod_body prod_postcondition prod_facts fenv X. 
      unfold triple_Imp_Lang in H21. 
      specialize (H21 (val2 :: val0 :: nil) init_nenv x H20 H1).
      invs H21. invs H23. invs H24. unfold prod_postcondition_prop in H32. 
      invs H31. 
      econstructor. econstructor. econstructor. 
      econstructor; try eassumption. 
      econstructor. econstructor; try eassumption.
      econstructor. econstructor; try simpl; try eassumption.
      econstructor.
      econstructor. 
      econstructor; try eassumption; try simpl.
      lia.
      econstructor; try eassumption.
      econstructor; try eassumption.
      econstructor.
      econstructor.
      unfold exp_invariant_prop. simpl.
      assert (v1 = val2). invs H29. simpl in H27. invs H27. reflexivity. rewrite H22 in *.
      assert (v2 = val0). invs H30. simpl in H28. invs H28. reflexivity. rewrite H26 in *.
      destruct H9.
      split; try lia.
      rewrite H9.
      assert ((val - (val1 - 1)) = 1 + (val - val1)).
         *  unfold Nat.add. invs H7. invs H32. invs H22. invs H33. 
            rewrite H28 in *. invs H37.
            pose proof leb_complete 1 n2 H28. 
            invs H38. 
            induction (nenv "x"). 
            simpl in H28. discriminate.
            assert (val1 = (S n)).
            eapply a_Imp_Lang_deterministic; eassumption.
            rewrite H26 in *.    
            simpl. lia.
         * rewrite H28. simpl. lia.
      + destruct H.
         *  invs H. econstructor. invs H0. invs H7. invs H2. invs H4. invs H8. rewrite H6 in *. 
         invs H3. invs H5. invs H9. invs H14. invs H18. invs H20. invs H22.
         econstructor. 
         (* rewrite H5 in *. *)
         econstructor; try eassumption.
         unfold exp_invariant_prop in H15; simpl in H15. destruct H15.  
         unfold exp_postcondition_prop.
         assert ((val - val1) = val). 
            -- invs H13. invs H12. 
               rewrite leb_iff_conv in H6.
               assert (nenv "x" = 0) by lia. 
               assert (nenv "x" = val1). 
               eapply a_Imp_Lang_deterministic; try eassumption.
               lia. 
            -- rewrite H11 in H1. symmetry. apply H1.
         * invs H.
Qed.     

Lemma partial_exp_correct : 
   forall fenv, 
      fenv "mult" = prod_function ->
      hl_Imp_Lang true_precondition exp_body exp_postcondition exp_facts fenv.
Proof.
   intros. unfold exp_body. econstructor. 
   -  econstructor. shelve. eapply (hl_Imp_Lang_assign exp_invariant).
      Unshelve. econstructor. econstructor.    
      remember (nth_error exp_facts 0) as eq1. 
      remember (nth_error exp_facts 0) as eq2.
      remember Heqeq1.
      clear Heqe.  
      rewrite Heqeq2 in Heqeq1. simpl in Heqeq1.
      rewrite Heqeq1 in e. rewrite Heqeq2 in e. symmetry in e. apply e. 
      eapply exp_fact_env_valid; try apply H.
      econstructor; reflexivity.   
   - unfold exp_loop. eapply hl_Imp_Lang_consequence_post. 
      econstructor. 
      +  econstructor. shelve. econstructor. Unshelve. 
         shelve. econstructor. econstructor.  
         remember (nth_error exp_facts 1) as eq1. 
         remember (nth_error exp_facts 1) as eq2.
         remember Heqeq1.
         clear Heqe.  
         rewrite Heqeq2 in Heqeq1. simpl in Heqeq1.
         rewrite Heqeq1 in e. rewrite Heqeq2 in e. symmetry in e. apply e. 
         eapply exp_fact_env_valid; try apply H. 
         unfold In; right; left; reflexivity. 
      +  remember (nth_error exp_facts 2) as eq1. 
         remember (nth_error exp_facts 2) as eq2.
         remember Heqeq1.
         clear Heqe.  
         rewrite Heqeq2 in Heqeq1. simpl in Heqeq1.
         rewrite Heqeq1 in e. rewrite Heqeq2 in e. symmetry in e. apply e.
      +  eapply exp_fact_env_valid; try apply H. unfold In; right; right; left; reflexivity.   
Defined.    


Lemma total_exp_correct : 
forall fenv, 
   fenv "mult" = prod_function ->
   forall n1 n2 dbenv nenv nenv', 
      AbsEnv_rel true_precondition fenv (n1::n2::dbenv) nenv -> 
      i_Imp_Lang exp_body (n1::n2::dbenv) fenv nenv nenv' ->
      nenv' "y" = n2 ^ n1.
Proof. 
   intros. pose proof partial_exp_correct fenv H. 
   pose proof Hoare_Imp_Lang_sound true_precondition exp_body exp_postcondition exp_facts fenv.
   unfold triple_Imp_Lang in H2. 
   specialize (H2 X (n1 :: n2 :: dbenv) nenv nenv' H1 H0). 
   invs H2. invs H4. invs H5. invs H10. simpl in H7. invs H7.
   invs H11. simpl in H9. invs H9. invs H12. 
   unfold exp_postcondition_prop in H13. symmetry. apply H13.
Qed.

Lemma exp_aexp_wrapper : 
   forall fenv dbenv nenv a1 a2 n1 n2, 
      fenv "mult" = prod_function -> 
      fenv "exp" = exp_function -> 
      a_Imp_Lang a1 dbenv fenv nenv n1 ->
      a_Imp_Lang a2 dbenv fenv nenv n2 ->
      a_Imp_Lang (APP_Imp_Lang "exp" (a1::a2::nil)) dbenv fenv nenv (n2^n1). 
Proof.
   intros. 
   pose proof exp_terminates (n1 :: n2 :: nil) init_nenv fenv.
   assert (AbsEnv_rel true_precondition fenv (n1 :: n2 :: nil) init_nenv) by (repeat (econstructor; try eassumption)).
   specialize (H3 H H4). invs H3.  
   econstructor.
   - exists.
   - rewrite H0. simpl. reflexivity.
   - repeat econstructor; try eassumption.    
   - rewrite H0. simpl. apply H5.
   - rewrite H0. simpl. 
      pose proof partial_exp_correct fenv. 
      pose proof Hoare_Imp_Lang_sound true_precondition exp_body exp_postcondition exp_facts fenv (X H).
      unfold triple_Imp_Lang in H6.  
      specialize (H6 (n1 :: n2 :: nil) init_nenv x H5 H4).
      invs H6. invs H8. invs H9. invs H14. simpl in *.
      invs H11.
      invs H15. simpl in *. invs H13.
      invs H16. 
      unfold exp_postcondition_prop in H17. 
      symmetry in H17. apply H17.
Qed.   
