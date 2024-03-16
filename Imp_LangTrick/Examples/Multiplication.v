From Coq Require Import String List Arith Psatz.

From Imp_LangTrick Require Import ProofCompiler StackLangTheorems ImpVarMap Imp_LangImpHigherOrderRel ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare Imp_LangImpHigherOrderRelTheorems LogicTranslationBase LogicTranslationAdequate StackLanguage.
(* From Imp_LangTrick Require Import ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed. *)
(* From Imp_LangTrick Require Import TranslationPure  *)
From Imp_LangTrick Require Import Imp_LangTrickLanguage ProofCompiler FactEnvTranslator.
(* From Imp_LangTrick Require Import ProofCompMod EnvToStack ProofCompAuto EnvToStackBuggy. *)
From Imp_LangTrick Require Import TerminatesForSure BuggyProofCompiler ProofCompCodeCompAgnosticMod.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Definition prod_loop : imp_Imp_Lang := WHILE_Imp_Lang (
   (LEQ_Imp_Lang (CONST_Imp_Lang 1) (VAR_Imp_Lang "x") ))
  (SEQ_Imp_Lang (ASSIGN_Imp_Lang "y" (PLUS_Imp_Lang (VAR_Imp_Lang "y") (PARAM_Imp_Lang 1))) (ASSIGN_Imp_Lang "x" (MINUS_Imp_Lang (VAR_Imp_Lang "x") (CONST_Imp_Lang 1)))).

Definition prod_body : imp_Imp_Lang := SEQ_Imp_Lang (SEQ_Imp_Lang (ASSIGN_Imp_Lang "x" (PARAM_Imp_Lang 0)) (ASSIGN_Imp_Lang "y" (CONST_Imp_Lang 0))) prod_loop.

Definition prod_function : fun_Imp_Lang :=
   {|Name := "mult"
   ; Args := 2
   ; Ret := "y"
   ; Body := prod_body|}. 



Definition prod_postcondition_prop : nat -> nat -> nat -> Prop :=
   fun x => fun y => fun z => x * y = z.
   
Definition prod_postcondition := 
   AbsEnvLP (Imp_Lang_lp_arith (TernaryProp nat aexp_Imp_Lang
      prod_postcondition_prop
         (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1) (VAR_Imp_Lang "y"))).
      
Definition true_precondition := 
   AbsEnvLP (Imp_Lang_lp_arith (BinaryProp nat aexp_Imp_Lang (fun x => fun y => True) (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1) )).

Definition product_invariant_prop : list nat -> Prop :=
   fun lst => 
   ((List.nth 3 lst 0) = 
      ((List.nth 0 lst 0) - (List.nth 2 lst 0)) * (List.nth 1 lst 0)) /\ 
      (List.nth 2 lst 0 <= List.nth 0 lst 0).

Definition product_invariant := 
   AbsEnvLP (Imp_Lang_lp_arith (NaryProp nat aexp_Imp_Lang
      product_invariant_prop
         ((PARAM_Imp_Lang 0)::(PARAM_Imp_Lang 1)::(VAR_Imp_Lang "x")::(VAR_Imp_Lang "y")::nil))).

Definition prod_facts : implication_env := 
         ((true_precondition,
         Imp_LangLogSubst.subst_AbsEnv "x" (PARAM_Imp_Lang 0)
            (Imp_LangLogSubst.subst_AbsEnv "y" (CONST_Imp_Lang 0)
               product_invariant)))
      ::
      (afalseImp_Lang
     ((LEQ_Imp_Lang (CONST_Imp_Lang 1) (VAR_Imp_Lang "x")))
     product_invariant, prod_postcondition)
      ::
      (atrueImp_Lang
     ((LEQ_Imp_Lang (CONST_Imp_Lang 1) (VAR_Imp_Lang "x")))
     product_invariant,
   Imp_LangLogSubst.subst_AbsEnv "y"
     (PLUS_Imp_Lang (VAR_Imp_Lang "y") (PARAM_Imp_Lang 1))
     (Imp_LangLogSubst.subst_AbsEnv "x"
        (MINUS_Imp_Lang (VAR_Imp_Lang "x") (CONST_Imp_Lang 1))
        product_invariant))
      ::
     nil. 

Lemma prod_fact_env_valid : 
   forall fenv, 
   fact_env_valid prod_facts fenv.
Proof. 
   intros. unfold fact_env_valid. intros.
   destruct H. simpl in *. invs H. 
   - econstructor. unfold true_precondition in *. 
      invs H0. invs H2. invs H3. 
      econstructor. econstructor. econstructor; try eassumption.
      econstructor; try eassumption. 
      econstructor; try eassumption. 
      econstructor. econstructor. econstructor. unfold product_invariant_prop. simpl. split. lia. lia.
   - destruct H. invs H.
      + econstructor. econstructor. unfold prod_postcondition_prop.
      invs H0. unfold product_invariant in H3. 
      invs H3. invs H2. invs H4. invs H8. invs H12. invs H14. invs H16. 
      unfold product_invariant_prop in H9. simpl in H9. destruct H9.
      invs H7. invs H9. invs H6. invs H20. rewrite H19 in *. invs H24.
      rewrite leb_iff_conv in H19. 
      assert (n2 = 0) by lia. rewrite H1 in *.
      pose proof a_Imp_Lang_deterministic dbenv fenv nenv 
      (VAR_Imp_Lang "x") val1 0 H13 H25.   
      econstructor; try eassumption. rewrite H17. lia.
      + destruct H. invs H.  
         * unfold Imp_LangLogSubst.subst_AbsEnv in *. simpl in *. econstructor. 
            invs H0. invs H3. invs H2. invs H4. invs H8. invs H12. invs H14. 
            invs H16. unfold product_invariant_prop in H9. simpl in H9.  
            invs H7. invs H5. invs H6. invs H20. rewrite H19 in *. invs H24.
            pose proof leb_complete 1 n2 H19. 
            pose proof a_Imp_Lang_deterministic dbenv fenv nenv (VAR_Imp_Lang "x") n2 val1 H25 H13. rewrite H17 in *. 
            (* invs H17. rewrite H17.   *)
            (* rewrite leb_iff_conv in H22.  *)
            econstructor.
            econstructor. 
            econstructor. eassumption.  
            econstructor. eassumption.
            econstructor. econstructor. eassumption.
            econstructor. econstructor. econstructor.
            eassumption. eassumption. econstructor.
            unfold product_invariant_prop. simpl. destruct H9. 
            split; try lia. 
            (* rewrite H1.  *)
            assert ((val - (val1 - 1)) = 1 + (val - val1)) by lia.
            rewrite H22. unfold Nat.add at 2. simpl. lia.
         * destruct H.
Qed.   
   
Lemma partial_prod_correct : 
   forall fenv, 
   hl_Imp_Lang true_precondition prod_body prod_postcondition prod_facts fenv. 
Proof. 
   intros. unfold prod_body. econstructor. 
   -  econstructor. shelve. 
      eapply (hl_Imp_Lang_assign product_invariant prod_facts fenv).
      Unshelve. econstructor. econstructor. 
      remember (nth_error prod_facts 0) as eq1. 
      remember (nth_error prod_facts 0) as eq2.
      remember Heqeq1.
      clear Heqe.  
      rewrite Heqeq2 in Heqeq1. simpl in Heqeq1.
      rewrite Heqeq1 in e. rewrite Heqeq2 in e. symmetry in e. apply e.
      eapply prod_fact_env_valid. econstructor. reflexivity. 
   - unfold prod_loop. eapply hl_Imp_Lang_consequence_post. econstructor. 
      econstructor. shelve. econstructor.     
      remember (nth_error prod_facts 1) as eq1. 
      remember (nth_error prod_facts 1) as eq2.
      remember Heqeq1.
      clear Heqe.  
      rewrite Heqeq2 in Heqeq1. simpl in Heqeq1.
      rewrite Heqeq1 in e. rewrite Heqeq2 in e. symmetry in e. apply e.
      eapply prod_fact_env_valid. unfold In. simpl. right. left. reflexivity.   
      Unshelve.
      econstructor. econstructor.
      remember (nth_error prod_facts 2) as eq1. 
      remember (nth_error prod_facts 2) as eq2.
      remember Heqeq1.
      clear Heqe.  
      rewrite Heqeq2 in Heqeq1. simpl in Heqeq1.
      rewrite Heqeq1 in e. rewrite Heqeq2 in e. symmetry in e. apply e.
      eapply prod_fact_env_valid. unfold In. simpl. right. right. left.
      reflexivity.   
Defined. 


Lemma prod_loop_terminates : 
   forall n dbenv nenv fenv, 
      AbsEnv_rel true_precondition fenv dbenv nenv -> 
      nenv "x" = n -> 
         exists nenv',
            i_Imp_Lang prod_loop dbenv fenv nenv nenv'.
Proof.
   induction n; intros; invs H; invs H2; invs H3; unfold prod_loop. 
   -  econstructor. eapply Imp_Lang_while_done. 
      (* pose proof Bool.negb_false_iff true. destruct H1. 
      rewrite <- H4; try reflexivity.  *)
      assert ((1 <=? (nenv "x")) = false). 
      eapply leb_iff_conv. lia. rewrite <- H1.    
      econstructor; try rewrite H1; repeat econstructor.   
   - assert (exists nenv'', i_Imp_Lang
         (WHILE_Imp_Lang
            ((LEQ_Imp_Lang (CONST_Imp_Lang 1) (VAR_Imp_Lang "x")))
            (SEQ_Imp_Lang
               (ASSIGN_Imp_Lang "y"
                  (PLUS_Imp_Lang (VAR_Imp_Lang "y") (PARAM_Imp_Lang 1)))
               (ASSIGN_Imp_Lang "x"
                  (MINUS_Imp_Lang (VAR_Imp_Lang "x") (CONST_Imp_Lang 1)))))
         dbenv fenv
         (update "x" (S n - 1) (update "y" (nenv "y" + v2) nenv)) 
         nenv'') as intermediate. 
         simpl. 
         specialize (IHn dbenv (update "x" (n - 0) (update "y" (nenv "y" + v2) nenv)) fenv). 
         assert (AbsEnv_rel true_precondition fenv dbenv
         (update "x" (n - 0) (update "y" (nenv "y" + v2) nenv))).
         econstructor. econstructor. econstructor.   
         +  invs H7. econstructor; try eassumption.
         +  invs H8. econstructor; try eassumption.
         +  apply H9.
         +  pose proof update_same nat "x" (n - 0) (update "y" (nenv "y" + v2) nenv).
            assert (n - 0 = n) by lia; rewrite H5 in *.  
            specialize (IHn H1 H4). 
            invs IHn. unfold prod_loop in H6. econstructor. apply H6.  
      + destruct intermediate as (nenv'', term). econstructor. eapply Imp_Lang_while_step.
         *  assert ((1 <=? (nenv "x")) = true).
            eapply leb_correct; lia.
            rewrite <- H1. 
            (* pose proof Bool.negb_true_iff false. destruct H1. 
            rewrite <- H4; try reflexivity.  *)
            econstructor; try rewrite H1; repeat econstructor.   
         *  econstructor; econstructor; econstructor.
            --  econstructor. exists.
            --  apply H8.
            --  econstructor. unfold update. simpl. apply H0.
            --  econstructor.
         * apply term.   
Qed. 

Lemma prod_terminates : 
   forall dbenv nenv fenv, 
      AbsEnv_rel true_precondition fenv dbenv nenv -> 
         exists nenv',
            i_Imp_Lang prod_body dbenv fenv nenv nenv'.
Proof. 
   intros. unfold true_precondition in H. invs H. invs H1. invs H2.
   unfold prod_body.
   pose proof prod_loop_terminates v1 dbenv (update "y" 0 (update "x" v1 nenv)) fenv. 
   assert (AbsEnv_rel true_precondition fenv dbenv
   (update "y" 0 (update "x" v1 nenv))).
   - econstructor. econstructor. econstructor.
      + invs H6. econstructor; eassumption.
      + invs H7. econstructor; eassumption.
      + apply H8.
   - specialize (H0 H3). 
      assert (update "y" 0 (update "x" v1 nenv) "x" = v1) by 
      (unfold update; simpl; reflexivity). 
      specialize (H0 H4). destruct H0. 
   econstructor. econstructor.
   econstructor. econstructor. eapply H6. econstructor. econstructor.
   apply H0.        
Qed. 
