From Coq Require Import Psatz Arith String List.

From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang SeriesExample FunctionWellFormed EnvToStackLTtoLEQ TranslationPure ProofCompMod StackLangTheorems ParamsWellFormed Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems Imp_LangDec Imp_LangLogPropDec UIPList StackLanguage.

Local Open Scope list_scope.
Local Open Scope string_scope.
From Imp_LangTrick Require Import ProofCompAutoAnother BloomFilterArrayProgram.
From Imp_LangTrick Require Import LogicProp Imp_LangLogProp Imp_LangLogHoare  ProofCompAuto ProofCompCodeCompAgnosticMod AimpWfAndCheckProofAuto StackLangTheorems Multiplication.
Local Open Scope imp_langtrick_scope.

From Imp_LangTrick Require Import ExponentiationCompiled MultiplicationCompiled MultWrappers.

Lemma target_exp_loop_terminates : 
  forall n stk, 
  StackLogicGrammar.absstate_match_rel TargetProd.precond TargetExp.fenv stk -> 
  nth_error stk 1 = Some n ->
  exists stk', 
    imp_stack_sem (While_Stk ((1 <=s (Var_Stk 2)))
    (Seq_Stk
       (Assign_Stk 1
          ("mult" @s (Var_Stk 1) :: (Var_Stk 4) :: nil))
       (Assign_Stk 2 ((Var_Stk 2) -s 1)))) TargetExp.fenv stk stk'
      /\
      nth_error stk 2 = nth_error stk' 2
      /\ 
      nth_error stk 3 = nth_error stk' 3
      /\
      skipn 2 stk = skipn 2 stk'.
Proof.
induction n; intros; invs H; invs H3; invs H6; invs H4; 
unfold LTtoLEQProofCompilable.SC.CC.compile_aexp in *; simpl in *;
destruct stk; simpl in H2; try lia;
destruct stk; simpl in H2; try lia;
destruct stk; simpl in H2; try lia;
destruct stk; simpl in H2; try lia. 
  econstructor; repeat split. econstructor. econstructor. econstructor.
  econstructor; simpl; try lia; try eassumption.
  econstructor. 
  reflexivity. reflexivity.
  reflexivity.
  specialize (IHn (n0 * n3 :: n1 - 1 :: n2 :: n3 :: stk)).
  assert (StackLogicGrammar.absstate_match_rel TargetProd.precond TargetExp.fenv
  (n0 * n3 :: n1 - 1 :: n2 :: n3 :: stk)).
  unfold TargetProd.precond. unfold TargetProd.CAPC.SC.comp_logic.
  simpl. econstructor. econstructor. simpl. lia.
  econstructor. econstructor. econstructor. lia.
  simpl; lia. simpl. reflexivity.
  econstructor; simpl; try lia.
  reflexivity. assumption.
  repeat econstructor.  
  specialize (IHn H1).
  simpl in IHn.
  invs H0.
  simpl in IHn.
  assert (n - 0 = n) by lia. rewrite H7 in *.  
  specialize (IHn eq_refl). invs IHn.
  destruct H8 as (H8, rest). 
econstructor. 
repeat split.           
eapply Stack_while_step.
shelve. shelve. apply H8.

Unshelve.
shelve. 
shelve.
shelve.
shelve.  
econstructor.
econstructor.
econstructor; simpl; try lia.
reflexivity.
econstructor.
(* simpl. reflexivity.
reflexivity. *)
econstructor.
econstructor; simpl; try lia.
pose proof target_mult_aexp_wrapper (n0 :: S n :: n2 :: n3 :: stk)
(Var_Stk 1) (Var_Stk 4) n0 n3.
apply H9.
econstructor; try simpl; try lia; reflexivity.    
econstructor; try simpl; try lia; reflexivity.
econstructor. reflexivity.
econstructor; try lia. simpl. lia. econstructor. 
econstructor; simpl; try lia. reflexivity. econstructor.
econstructor; simpl; try lia.
assert (n = n - 0) by lia. rewrite <- H9. 
econstructor. reflexivity.
Unshelve.             

destruct rest.
apply H9.
destruct rest. apply H13.
apply rest.
Qed.                



Lemma target_exp_terminates :
  forall stk, 
  StackLogicGrammar.absstate_match_rel TargetExp.precond TargetExp.fenv stk -> 
  exists stk', 
    imp_stack_sem TargetExp.program TargetExp.fenv stk stk'
    /\
    nth_error stk 2 = nth_error stk' 2
    /\ 
    nth_error stk 3 = nth_error stk' 3
    /\
    skipn 2 stk = skipn 2 stk'.
Proof. 
  intros. invs H; invs H2; invs H5; invs H3; 
  unfold LTtoLEQProofCompilable.SC.CC.compile_aexp in *; simpl in *; 
  destruct stk; simpl in H1; try lia;
  destruct stk; simpl in H1; try lia;
  destruct stk; simpl in H1; try lia;
  destruct stk; simpl in H1; try lia.
  unfold TargetExp.program. simpl.  
  pose proof target_exp_loop_terminates n1 (1 :: n1 :: n1 :: n2 :: stk).
  assert (StackLogicGrammar.absstate_match_rel TargetProd.precond TargetExp.fenv (1 :: n1 :: n1 :: n2 :: stk)).
  econstructor. econstructor. simpl; lia.
  econstructor. econstructor. econstructor; simpl; try lia.
  reflexivity.
  econstructor; simpl; try lia.
  reflexivity. auto.
  repeat econstructor.
  specialize (H0 H6 eq_refl). invs H0.               
  econstructor; repeat split. unfold TargetExp.program.
  unfold compile_imp. simpl.
  econstructor.
  econstructor. econstructor; simpl. lia. lia.    
  econstructor; simpl; try lia.
  reflexivity. 
  econstructor; simpl; try lia.
  shelve.
  shelve.
  econstructor. reflexivity.
  Unshelve.
  reflexivity.
  econstructor; simpl; try lia.
  econstructor. econstructor.
  reflexivity.
  apply H7.
  shelve. shelve.  shelve. 
  simpl. lia.
  simpl. lia.
  Unshelve.
  destruct H7.
  destruct H8.
  eassumption.
  destruct H7. destruct H8.
  destruct H12.  
  eassumption.
  destruct H7. destruct H8. destruct H12.
  simpl in H13. 
  apply H13. 
Qed.

Lemma target_exp_aexp_wrapper : 
   forall stk a1 a2 n1 n2, 
      aexp_stack_sem a1 TargetExp.fenv stk (stk, n1) ->
      aexp_stack_sem a2 TargetExp.fenv stk (stk, n2) ->
      aexp_stack_sem (App_Stk "exp" (a1::a2::nil)) TargetProd.fenv stk (stk, n2 ^ n1). 
Proof.
  intros. 
  
  (* destruct stk. simpl in H1; try lia;
  destruct stk; simpl in H1; try lia;
  destruct stk; simpl in H1; try lia;
  destruct stk; simpl in H1; try lia.
  pose proof big_funcs_okay_too.
  unfold funcs_okay_too in H1.
  simpl in H1.     *)
  
  assert (StackLogicGrammar.absstate_match_rel TargetProd.precond TargetProd.fenv
  (0 :: 0 :: n1 :: n2 :: stk)).
econstructor. econstructor. simpl. lia.
econstructor. econstructor. 
econstructor; simpl; try lia; try reflexivity. 
econstructor; simpl; try lia; try reflexivity.
auto.
repeat econstructor.   
pose proof (target_exp_terminates (0 :: 0 :: n1 :: n2 :: stk) H1). invs H2.
destruct H3 as (H3, rest). destruct rest as (rest1, rest2).
destruct rest2 as (rest2, rest3). 
  econstructor. 
  - unfold TargetProd.fenv.
  unfold series_fenv. unfold imp_fenv_ify. unfold compile_fenv. 
  simpl. unfold compile_function. simpl. reflexivity.
  - reflexivity. 
  - reflexivity. 
  - reflexivity. 
  - reflexivity.
  - econstructor; try eassumption.
    econstructor; try eassumption.
    econstructor. 
  - simpl. econstructor.
    + econstructor. reflexivity.
    + econstructor. econstructor. reflexivity.
      apply H3. 
  - simpl. 
  pose proof CompiledExpProof.compiled.
  pose proof StackLogic.Hoare_stk_sound CompiledExpProof.T.precond
  CompiledExpProof.T.program CompiledExpProof.T.postcond
  CompiledExpProof.T.facts CompiledExpProof.T.fenv X.
  unfold StackLogic.triple_stk in H4.  
  specialize (H4 (0 :: 0 :: n1 :: n2 :: stk) x H3 H1). 
  invs H4.
  invs H10.
  invs H6; unfold LTtoLEQProofCompilable.SC.CC.compile_aexp in *; simpl in *.   
  unfold exp_postcondition_prop in H17.
  invs H14. simpl in H19. rewrite H19 in rest1.
  invs H15. simpl in H21. rewrite H21 in rest2.
  invs rest1. invs rest2.
  unfold stack_mapping; simpl.
  apply H16.
  - simpl. 
  pose proof CompiledExpProof.compiled.
  pose proof StackLogic.Hoare_stk_sound CompiledExpProof.T.precond
  CompiledExpProof.T.program CompiledExpProof.T.postcond
  CompiledExpProof.T.facts CompiledExpProof.T.fenv X.
  unfold StackLogic.triple_stk in H4.  
  specialize (H4 (0 :: 0 :: n1 :: n2 :: stk) x H3 H1). 
  invs H4.
  invs H10.
  invs H6; unfold LTtoLEQProofCompilable.SC.CC.compile_aexp in *; simpl in *.   
  unfold exp_postcondition_prop in H17.
  invs H14. simpl in H19. rewrite H19 in rest1.
  invs H15. simpl in H21. rewrite H21 in rest2.
  invs rest1. invs rest2.
  destruct x; simpl in H17; try discriminate. 
  destruct x; simpl in H17; try discriminate. 
  destruct x; simpl in H17; try discriminate. 
  destruct x; simpl in H17; try discriminate. 
  econstructor.
  econstructor.
  rewrite <- rest3. 
  econstructor. econstructor. econstructor. reflexivity.      
Qed. 
