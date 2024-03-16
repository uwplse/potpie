From Coq Require Import String List Arith Psatz.

From Imp_LangTrick Require Import ProofCompiler StackLangTheorems ImpVarMap Imp_LangImpHigherOrderRel ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare Imp_LangImpHigherOrderRelTheorems LogicTranslationBase LogicTranslationAdequate StackLanguage.
From Imp_LangTrick Require Import
     (* ProofCompilerPostHelpers *)
     FunctionWellFormed.
(* ParamsWellFormed. *)
From Imp_LangTrick Require Import TranslationPure.
From Imp_LangTrick Require Import Imp_LangTrickLanguage ProofCompiler FactEnvTranslator EnvToStackLTtoLEQ.
(* From Imp_LangTrick Require Import ProofCompMod EnvToStack ProofCompAuto EnvToStackBuggy. *)
From Imp_LangTrick Require Import TerminatesForSure BuggyProofCompiler ProofCompCodeCompAgnosticMod ImpExampleHelpers SeriesExample ProofCompAuto.

From Imp_LangTrick Require Import rsa_impLang.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Lemma big_fenv_well_formed : 
  fenv_well_formed' (prod_function :: exp_function :: fraction_addition_denominator_fun :: fraction_addition_numerator_fun :: fraction_subtraction_numerator_fun ::
  (init_fenv "id") :: nil) series_fenv.
Proof.
  econstructor.
  - repeat (econstructor; try simpl; try unfold not; intros; repeat (destruct H; try discriminate)).
  - repeat split.
    + unfold series_fenv in H. unfold imp_fenv_ify in H.
        simpl in H. unfold update in H. unfold init_fenv in *. rewrite H.
      destruct (string_dec f "mult"); destruct (string_dec f "exp");
      destruct (string_dec f "frac_add_denominator"); 
      destruct (string_dec f "frac_add_numerator"); 
      destruct (string_dec f "frac_sub_numerator"); subst; try discriminate.
      * simpl. left. left. reflexivity.
      * simpl. left. right. left. reflexivity.
      * simpl. left. right. right. left. reflexivity.
      * simpl. left. right. right. right. left. reflexivity.
      * simpl. left. right. right. right. right. left. reflexivity. 
      * right. unfold not in *. 
      destruct string_dec. symmetry in e. specialize (n e). contradiction.
      destruct string_dec. symmetry in e. specialize (n0 e). contradiction.
      destruct string_dec. symmetry in e. specialize (n1 e). contradiction.
      destruct string_dec. symmetry in e. specialize (n2 e). contradiction.
      destruct string_dec. symmetry in e. specialize (n3 e). contradiction.
      destruct string_dec; 
      reflexivity.
    + unfold series_fenv in H. unfold imp_fenv_ify in H.
      simpl in H. unfold update in H. unfold init_fenv in *. rewrite H. 
      destruct string_dec. repeat econstructor.         
      destruct string_dec. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor. econstructor. 
      econstructor. econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor. econstructor. eapply ImpVarMap.ImpHasVarSeq__right. 
      econstructor. reflexivity. 
      econstructor.
      simpl. reflexivity.
      (* left. simpl. reflexivity. *)
      econstructor. econstructor. econstructor. econstructor.
      destruct string_dec. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor.
      eapply ImpVarMap.ImpHasVarSeq__right. econstructor.
      simpl. reflexivity.
      left. simpl. reflexivity.
      destruct string_dec. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor. econstructor. 
      eapply ImpVarMap.ImpHasVarSeq__right. econstructor.
      simpl. reflexivity.
      left. simpl. reflexivity.  
      econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. 
      eapply ImpVarMap.ImpHasVarSeq__right. econstructor. 
      simpl. reflexivity.
      left. simpl. reflexivity.
      destruct string_dec. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor. econstructor. 
      eapply ImpVarMap.ImpHasVarSeq__right. econstructor.
      simpl. reflexivity.
      left. simpl. reflexivity.  
      econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. econstructor. econstructor.
      econstructor. econstructor. econstructor. 
      eapply ImpVarMap.ImpHasVarSeq__right. econstructor. 
      simpl. reflexivity.
      left. simpl. reflexivity.
      destruct string_dec. simpl. econstructor. econstructor.    
      simpl. econstructor. econstructor.
    + rewrite H. unfold series_fenv.
      simpl. unfold update.
      destruct string_dec.
      simpl. econstructor. eapply ImpVarMap.ImpHasVarSeq__right. econstructor.
      simpl. reflexivity.
      destruct string_dec.  
      simpl. econstructor. eapply ImpVarMap.ImpHasVarSeq__right. econstructor.
      simpl. reflexivity.
      destruct string_dec.  
      simpl. econstructor. simpl. econstructor.
      destruct string_dec.  
      simpl. econstructor. simpl. econstructor.
      destruct string_dec. 
      simpl. econstructor. simpl. econstructor.
      destruct string_dec. 
      simpl. econstructor. simpl. econstructor.
      econstructor. econstructor.  
    + simpl. finite_nodup. 
    + simpl. intros. try unfold series_fenv in *; try simpl in *;
      unfold update in *. rewrite H0.
      destruct string_dec. simpl in *. symmetry. apply e.
      destruct string_dec. simpl in *. symmetry. apply e.
      destruct string_dec. simpl in *. symmetry. apply e.
      destruct string_dec. simpl in *. symmetry. apply e.
      destruct string_dec. simpl in *. symmetry. apply e.
      destruct string_dec. simpl in *. symmetry. apply e.

      destruct IN_FUNC_NAMES. intuition.
      destruct H1. intuition.
      destruct H1. intuition.
      destruct H1. intuition.
      destruct H1. intuition. 
      destruct H1. intuition. 
      contradiction.
    + repeat unfold In. right. right. right. right. right. left. reflexivity.
    + unfold not. simpl. intros. unfold series_fenv. simpl. unfold update.
      destruct string_dec. intuition.
      destruct string_dec. intuition.
      destruct string_dec. intuition.
      destruct string_dec. intuition.
      destruct string_dec. intuition.
      destruct string_dec. intuition.

      econstructor.
    + intros. unfold series_fenv in *. simpl in *. unfold update in *.
      destruct string_dec. exists f.
      split. left. apply e. split. rewrite <- e. simpl. reflexivity. 
      rewrite H. simpl. rewrite e. reflexivity.

      destruct string_dec. exists f.
      split. right. left. apply e. split. rewrite <- e. simpl. reflexivity. 
      rewrite H. simpl. rewrite e. reflexivity.

      destruct string_dec. exists f.
      split. right. right. left. apply e. split. rewrite <- e. simpl. reflexivity. 
      rewrite H. simpl. rewrite e. reflexivity.

      destruct string_dec. exists f.
      split. right. right. right. left. apply e. split. rewrite <- e. simpl. reflexivity. 
      rewrite H. simpl. rewrite e. reflexivity.

      destruct string_dec. exists f.
      split. right. right. right. right. left. apply e. split. rewrite <- e. simpl. reflexivity. 
      rewrite H. simpl. rewrite e. reflexivity.

      destruct string_dec. exists f.
      split. right. right. right. right. right. left. apply e. split. rewrite <- e. simpl. reflexivity. 
      rewrite H. simpl. rewrite e. reflexivity.

      exists "id". split; try split.
      right. right. right. right. right. left. reflexivity.
      simpl. unfold init_fenv in *. reflexivity.
      unfold init_fenv in H. rewrite H. simpl. reflexivity.    
Qed. 

Lemma big_funcs_okay_too :
  funcs_okay_too (prod_function :: exp_function :: fraction_addition_denominator_fun :: fraction_addition_numerator_fun :: fraction_subtraction_numerator_fun ::
  (init_fenv "id") :: nil) (compile_fenv series_fenv). 
Proof. 
unfold series_fenv. unfold imp_fenv_ify. simpl. 
unfold compile_fenv. econstructor; try split; try split. 
  - repeat econstructor.
  (* - intros; repeat econstructor. simpl.  
  - repeat econstructor. *)
  - intros. unfold update. 
    destruct string_dec. simpl. symmetry; assumption.
    destruct string_dec. simpl. symmetry; assumption.
    destruct string_dec. simpl. symmetry; assumption.
    destruct string_dec. simpl. symmetry; assumption.
    destruct string_dec. simpl. symmetry; assumption.
    destruct string_dec. simpl. symmetry; assumption.

    destruct H. rewrite <- H in *. simpl in *. contradiction. 
    destruct H. rewrite <- H in *. simpl in *. contradiction. 
    destruct H. rewrite <- H in *. simpl in *. contradiction. 
    destruct H. rewrite <- H in *. simpl in *. contradiction.
    destruct H. rewrite <- H in *. simpl in *. contradiction.
    destruct H. rewrite <- H in *. simpl in *. contradiction.
    destruct H. 
  - intros. unfold update.
    destruct string_dec. left. simpl. left. assumption.
    destruct string_dec. left. simpl. right. left. assumption.
    destruct string_dec. left. simpl. right. right. left. assumption.
    destruct string_dec. left. simpl. right. right. right. left. assumption.
    destruct string_dec. left. simpl. right. right. right. right.  left. assumption.
    destruct string_dec. left. simpl. right. right. right. right. right. left. assumption.
    right. unfold init_fenv. unfold compile_function. simpl. 
    unfold init_fenv_stk. unfold stack_mapping. simpl. reflexivity.     
Qed. 
