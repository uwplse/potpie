From Coq Require Import List String Arith Psatz.


From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage FactEnvTranslator ProofCompAuto TerminatesForSure ProofCompCodeCompAgnosticMod ProofCompAutoAnother.
From Imp_LangTrick Require Import StackLangTheorems ImpVarMap ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed TranslationPure Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems.
From Imp_LangTrick Require Import SeriesExampleProofInputs.
From Imp_LangTrick Require Import EnvToStackLTtoLEQ.
From Imp_LangTrick Require Import SeriesExample.
From Imp_LangTrick Require Import SeriesHelperCompilation.
From Imp_LangTrick.Tactics Require Import MiscTactics.
From Imp_LangTrick Require Import StackFrameReflection StackPurestBaseReflection HelperWrappers.
Local Open Scope string_scope.

Lemma target_frac_add_denominator_wrapper : 
  forall stk a1 a2 n1 n2, 
  aexp_stack_sem a1 TargetProd.fenv stk  (stk, n1) ->
  aexp_stack_sem a2 TargetProd.fenv stk  (stk, n2) ->
  aexp_stack_sem (App_Stk "frac_add_denominator"%string (a1::a2::nil)) TargetProd.fenv stk (stk, (n1 * n2)).
Proof. 
  intros.  
  econstructor; simpl; try reflexivity; unfold TargetProd.fenv; simpl.
  econstructor; try eassumption.
  econstructor; try eassumption.
  econstructor. simpl. econstructor. econstructor.
  reflexivity. 
  econstructor. unfold stack_mapping. simpl. reflexivity.
  unfold stack_mapping. simpl. lia.
  eapply target_mult_aexp_wrapper.
  econstructor; simpl; simpl; try lia; try reflexivity.        
  econstructor; simpl; simpl; try lia; try reflexivity.
  econstructor. reflexivity.  
  unfold stack_mapping. simpl. 
  econstructor; simpl; simpl; try lia; try reflexivity.
  repeat econstructor.
Qed.          

Lemma target_frac_add_numerator_wrapper : 
  forall stk a1 a2 a3 a4 n1 n2 n3 n4, 
  aexp_stack_sem a1 TargetProd.fenv stk  (stk, n1) ->
  aexp_stack_sem a2 TargetProd.fenv stk  (stk, n2) ->
  aexp_stack_sem a3 TargetProd.fenv stk  (stk, n3) ->
  aexp_stack_sem a4 TargetProd.fenv stk  (stk, n4) ->
  aexp_stack_sem (App_Stk "frac_add_numerator"%string (a1::a2::a3::a4::nil)) TargetProd.fenv stk (stk, ((n1 * n4) + (n2 * n3))). 
Proof.
  intros.
  econstructor; simpl; try reflexivity; unfold TargetProd.fenv; simpl.
  econstructor; try eassumption.
  econstructor; try eassumption.
  econstructor; try eassumption.
  econstructor; try eassumption.
  econstructor. simpl. econstructor. econstructor.
  reflexivity.
  econstructor. unfold stack_mapping. simpl. reflexivity.
  unfold stack_mapping. simpl. lia.
  econstructor.
  eapply target_mult_aexp_wrapper.
  econstructor; simpl; simpl; try lia; try reflexivity.        
  econstructor; simpl; simpl; try lia; try reflexivity.
  eapply target_mult_aexp_wrapper.
  econstructor; simpl; simpl; try lia; try reflexivity.        
  econstructor; simpl; simpl; try lia; try reflexivity.
  unfold stack_mapping. simpl.
  econstructor. exists.
  unfold stack_mapping. simpl.
  econstructor; simpl; try lia; try reflexivity.
  assert (n3 * n2 = n2 * n3) as eq by lia; rewrite eq.
  reflexivity.
  repeat econstructor.
Qed.
