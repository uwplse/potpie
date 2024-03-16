From Coq Require Import String List Arith Psatz.

From Imp_LangTrick Require Import ProofCompiler StackLangTheorems ImpVarMap Imp_LangImpHigherOrderRel ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare Imp_LangImpHigherOrderRelTheorems LogicTranslationBase LogicTranslationAdequate StackLanguage.
From Imp_LangTrick Require Import ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed.
From Imp_LangTrick Require Import TranslationPure Imp_LangTrickLanguage.
From Imp_LangTrick Require Import ProofCompiler FactEnvTranslator.
From Imp_LangTrick Require Import ProofCompMod EnvToStack ProofCompAuto EnvToStackBuggy.
From Imp_LangTrick Require Import TerminatesForSure BuggyProofCompiler ProofCompCodeCompAgnosticMod.

From Imp_LangTrick Require Export Multiplication Exponentiation.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.




(*euc_div x y = x mod y*)
Definition euc_div_loop : imp_Imp_Lang := WHILE_Imp_Lang (
   (LEQ_Imp_Lang (PARAM_Imp_Lang 1) (VAR_Imp_Lang "x")))
   (ASSIGN_Imp_Lang "x" (MINUS_Imp_Lang (VAR_Imp_Lang "x") (PARAM_Imp_Lang 1))).

Definition euc_div_body : imp_Imp_Lang := (SEQ_Imp_Lang (ASSIGN_Imp_Lang "x" (PARAM_Imp_Lang 0))) euc_div_loop.

(*encode p q pubk privk message = message encoded under the public key mod pq*)
(* Definition encode_body : imp_Imp_Lang := 
   SEQ_Imp_Lang 
      (ASSIGN_Imp_Lang "mod" 
         (APP_Imp_Lang "mult" ((PARAM_Imp_Lang 0)::(PARAM_Imp_Lang 1)::nil)))
      (ASSIGN_Imp_Lang "ciphertext"
         (APP_Imp_Lang "euc_div" 
            ((APP_Imp_Lang "exp" ((PARAM_Imp_Lang 4)::(PARAM_Imp_Lang 2)::nil))
         ::(VAR_Imp_Lang "mod")::nil))).  *)

(*decode p q pubk privk ct = ct decoded under the privk mod pq*)
(* Definition decode_body : imp_Imp_Lang := 
   SEQ_Imp_Lang 
      (ASSIGN_Imp_Lang "mod" 
         (APP_Imp_Lang "mult" ((PARAM_Imp_Lang 0)::(PARAM_Imp_Lang 1)::nil)))
      (ASSIGN_Imp_Lang "plaintext"
         (APP_Imp_Lang "euc_div" 
            ((APP_Imp_Lang "exp" ((PARAM_Imp_Lang 4)::(PARAM_Imp_Lang 3)::nil))
         ::(VAR_Imp_Lang "mod")::nil))).  *)

   (* mod := p * q; *)
   (* ciphertext := euc_div(exp(message pubk) mod) *)


Definition mod_postcondition_prop : nat -> nat -> nat -> Prop :=
   fun x => fun y => fun z => x mod y = z.
   
Definition mod_postcondition := 
   AbsEnvLP (Imp_Lang_lp_arith (TernaryProp nat aexp_Imp_Lang
      mod_postcondition_prop
         (PARAM_Imp_Lang 0) (PARAM_Imp_Lang 1) (VAR_Imp_Lang "x"))).

Definition mod_invariant_prop : list nat -> Prop :=
   fun lst => 
   (((List.nth 2 lst 0) mod (List.nth 1 lst 0)) = 
   ((List.nth 0 lst 0) mod (List.nth 1 lst 0))) /\ 
      (List.nth 2 lst 0 <= List.nth 0 lst 0).

Definition mod_invariant := 
   AbsEnvLP (Imp_Lang_lp_arith (NaryProp nat aexp_Imp_Lang
      mod_invariant_prop
         ((PARAM_Imp_Lang 0)::(PARAM_Imp_Lang 1)::(VAR_Imp_Lang "x")::nil))).

Definition mod_facts : implication_env := 
   (true_precondition, (Imp_LangLogSubst.subst_AbsEnv "x" (PARAM_Imp_Lang 0) mod_invariant))
   ::
   (atrueImp_Lang (LEQ_Imp_Lang (PARAM_Imp_Lang 1) (VAR_Imp_Lang "x")) mod_invariant,
   Imp_LangLogSubst.subst_AbsEnv "x" (MINUS_Imp_Lang (VAR_Imp_Lang "x") (PARAM_Imp_Lang 1)) mod_invariant)
   ::
   (afalseImp_Lang (LEQ_Imp_Lang (PARAM_Imp_Lang 1) (VAR_Imp_Lang "x")) mod_invariant, mod_postcondition)
   ::
   nil. 

Lemma partial_mod_correct : 
   forall fenv, 
      hl_Imp_Lang true_precondition euc_div_body mod_postcondition mod_facts fenv.
Proof.
   intros. unfold euc_div_body. econstructor.
   - eapply hl_Imp_Lang_consequence_pre. shelve. 
      remember (nth_error mod_facts 0) as eq1. 
      remember (nth_error mod_facts 0) as eq2.
      remember Heqeq1.
      clear Heqe.  
      rewrite Heqeq2 in Heqeq1. simpl in Heqeq1.
      rewrite Heqeq1 in e. rewrite Heqeq2 in e. symmetry in e. apply e.
      econstructor. invs H. invs H1. invs H2. econstructor. econstructor. 
      econstructor. apply H6. 
      econstructor. apply H7. 
      econstructor. apply H6. econstructor. 
      unfold mod_invariant_prop; simpl. 
      split; auto.
      Unshelve. shelve. 
      assert ((Imp_LangLogSubst.subst_AbsEnv "x" (PARAM_Imp_Lang 0) mod_invariant) = (AbsEnvLP
      (Imp_Lang_lp_arith
         (NaryProp nat aexp_Imp_Lang mod_invariant_prop
            (PARAM_Imp_Lang 0 :: PARAM_Imp_Lang 1 :: PARAM_Imp_Lang 0 :: nil))))) by (simpl; reflexivity). 
      rewrite <- H. econstructor.
   - eapply hl_Imp_Lang_consequence_post.
      + unfold euc_div_loop. econstructor. 
         econstructor. econstructor.  
         remember (nth_error mod_facts 1) as eq1. 
         remember (nth_error mod_facts 1) as eq2.
         remember Heqeq1.
         clear Heqe.  
         rewrite Heqeq2 in Heqeq1. simpl in Heqeq1.
         rewrite Heqeq1 in e. rewrite Heqeq2 in e. symmetry in e. apply e.
         econstructor. 
         invs H. invs H2. invs H1. invs H3. invs H7. invs H11. invs H13.
         invs H6. invs H4. invs H5. invs H17. rewrite H16 in *.    
         econstructor. econstructor. 
         econstructor. simpl; try eassumption.         
         econstructor. simpl; try eassumption.
         econstructor. simpl. econstructor; try eassumption.
         econstructor. unfold mod_invariant_prop in *; simpl in *.
         assert (val1 = n2) by (eapply a_Imp_Lang_deterministic; eassumption). 
         destruct H8. rewrite H0 in *.  
         split; try lia.
         assert (val0 = n1) by (eapply a_Imp_Lang_deterministic; eassumption). 
         rewrite H18 in *.
         pose proof leb_complete n1 n2 H16.
         rewrite <- H8 in *.
         assert ((((n2 - n1) + n1) mod n1) = (n2 - n1) mod n1).
         induction n1. 
         * simpl. lia.
         * rewrite Nat.add_mod. 
            rewrite Nat.mod_same. 
            assert (((n2 - S n1) mod S n1 + 0) = ((n2 - S n1) mod S n1)) by lia.
            rewrite H20.   
            rewrite Nat.mod_mod. reflexivity.  
            auto. auto. auto.
         * rewrite <- H20.
            assert ((n2 - n1 + n1) = n2) by lia.
            rewrite H23. reflexivity.   
      + remember (nth_error mod_facts 2) as eq1. 
         remember (nth_error mod_facts 2) as eq2.
         remember Heqeq1.
         clear Heqe.  
         rewrite Heqeq2 in Heqeq1. simpl in Heqeq1.
         rewrite Heqeq1 in e. rewrite Heqeq2 in e. symmetry in e. apply e.
      + econstructor. 
         invs H. invs H2. invs H1. invs H3. invs H7. invs H11. invs H13.    
         invs H6. invs H4. invs H5. invs H17. rewrite H16 in *.
         econstructor. econstructor; try eassumption. 
         unfold mod_invariant_prop in H8; simpl in H8. destruct H8.  
         unfold mod_postcondition_prop in *; simpl in *.
         assert (val0 = n1) by (eapply a_Imp_Lang_deterministic; eassumption).
         rewrite H14 in *. 
         assert (val1 = n2) by (eapply a_Imp_Lang_deterministic; eassumption).
         rewrite H18 in *. 
         rewrite leb_iff_conv in H16. 
         assert (n2 mod n1 = n2) by (eapply Nat.mod_small; eassumption).
         rewrite <- H19. symmetry. apply H0.    
Qed.


Lemma mult_aexp_wrapper : 
   forall fenv dbenv nenv a1 a2 n1 n2, 
      fenv "mult" = prod_function -> 
      a_Imp_Lang a1 dbenv fenv nenv n1 ->
      a_Imp_Lang a2 dbenv fenv nenv n2 ->
      a_Imp_Lang (APP_Imp_Lang "mult" (a1::a2::nil)) dbenv fenv nenv (n1 * n2). 
Proof.
   intros. 
   pose proof prod_terminates (n1 :: n2 :: nil) init_nenv fenv.
   assert (AbsEnv_rel true_precondition fenv (n1 :: n2 :: nil) init_nenv) by (repeat (econstructor; try eassumption)).
   specialize (H2 H3). invs H2.  
   econstructor.
   - exists.
   - rewrite H. simpl. reflexivity.
   - repeat econstructor; try eassumption.    
   - rewrite H. simpl. apply H4.
   - rewrite H. simpl. 
      pose proof partial_prod_correct fenv. 
      pose proof Hoare_Imp_Lang_sound true_precondition prod_body prod_postcondition prod_facts fenv X.
      unfold triple_Imp_Lang in H5.  
      specialize (H5 (n1 :: n2 :: nil) init_nenv x H4 H3).
      invs H5. invs H7. invs H8. invs H13. simpl in *.
      invs H10.
      invs H14. simpl in *. invs H12.
      invs H15. 
      unfold prod_postcondition_prop in H16. 
      symmetry in H16. apply H16.
Qed.   

