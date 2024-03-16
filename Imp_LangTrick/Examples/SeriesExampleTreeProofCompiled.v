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

Module SeriesProofCompilationPluginOnly(S: SeriesProgramInputs).
  Module SeriesSourceProgram <: ProofCompMod.SourceProgramType.
    Include S.
    Definition program := series_calculation_program x dn dd.
    Definition precond := series_precond x dn dd.
    Definition postcond := series_postcond x dn dd.
    Definition fenv := series_fenv.
    Definition facts := series_program_facts x dn dd.
    Definition hoare_triple := series_hoare_triple x dn dd.
    Definition idents := construct_trans program.
    Definition num_args := 0.
    Definition funcs := series_funcs.
  End SeriesSourceProgram.

  Module SeriesTargetProgramInputs <: TargetProgramInputs.
    Definition target_fenv : fun_env_stk := compile_fenv series_fenv.
    Definition target_facts idents args : StackLogic.implication_env_stk :=
      map (fun (x: (AbsEnv * AbsEnv)) =>
             let (P, Q) := x in
             (LTtoLEQCompilerAgnostic.SC.comp_logic args idents P, LTtoLEQCompilerAgnostic.SC.comp_logic args idents Q))
          SeriesSourceProgram.facts.
  End SeriesTargetProgramInputs.

  Module SeriesTargetProgram := CompilerAgnosticProofCompilableTargetProgram (SeriesSourceProgram) (LTtoLEQCompilerAgnostic.PC.CC) (LTtoLEQCompilerAgnostic.PC.SC) (SeriesTargetProgramInputs).
  Module SeriesActualProofCompilation.

  (* Declare Module CAPC : CompilerAgnosticProofCompilerType. *)
  (* Declare Module SOURCE : SourceProgramType. *)
  (* Declare Module TARGET : TargetProgramType. *)
  Module CAPC := LTtoLEQCompilerAgnostic (* Whatever the < to <= compiler agnostic proof compiler module is called *).
  Module SOURCE := SeriesSourceProgram.
  Module TARGET := SeriesTargetProgram.

  

  Lemma pre_sound : CAPC.SC.transrelation_sound SOURCE.precond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    econstructor. intros. CAPC.PC.unfold_cc_sc; split; intros.
    - simpl. meta_smash.
      + unfold SOURCE.precond in H1. unfold SOURCE.idents in H0. unfold construct_trans in H0. simpl in H0.
        destruct_stks stk.
        simpl. lia.
      + unfold SOURCE.precond in H1. unfold series_precond in H1.
        destruct_stks stk.
        invc H1. invc H4. invc H8. invc H2. invc H3. invc H4. invc H2. invc H8. invc H9. invc H10. destruct H11 as (A & B & C & D & E & F).
        intuition.
      + econstructor; prove_exp_stack_pure_rel.
      + destruct_stks stk. simpl. lia.
      + repeat split; reflexivity.
      + econstructor; prove_exp_stack_pure_rel.
    - simpl in H1. invc H1. invc H4. invc H8. invc H7. invc H2. invc H10. invc H2. invc H5. invc H11. invc H12. invc H13. invc H15. invc H16. invc H17. unfold SOURCE.precond. unfold series_precond. econstructor; econstructor; econstructor; econstructor; meta_smash.
      eassumption. intuition.
  Qed.
  
  Lemma post_sound : CAPC.SC.transrelation_sound SOURCE.postcond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    unfold SOURCE.postcond. unfold series_postcond. unfold SOURCE.idents. unfold SOURCE.program. unfold series_calculation_program. simpl.
    unfold construct_trans. simpl. econstructor.
    intros. simpl. unfold LTtoLEQProofCompilable.SC.CC.compile_aexp. simpl. destruct_stks stk.
    split; intros.
    - invc H1. invc H3. invc H2. invc H6. invc H7. meta_smash.
      + lia.
      + econstructor; prove_exp_stack_pure_rel.
    - invc H1. invc H4. invc H7. invc H3. invc H8. invc H9. simpl in H12. invc H12. simpl in H14. invc H14.
      econstructor. econstructor. econstructor; meta_smash.
  Qed.

  Ltac aexp_stack_sem_same :=
    match goal with
    | [ H1: aexp_stack_sem ?a ?fenv ?stk (?stk1, ?v1),
          H2: aexp_stack_sem ?a ?fenv ?stk (?stk2, ?v2) |- _ ] =>
        let DET := fresh "DET" in
        pose proof (DET := aexp_stack_sem_det fenv stk a (stk1, v1) (stk2, v2) H1 H2)
    end.

  Ltac apply_target_mult_aexp_wrapper H :=
    let Htype := type of H in
    idtac Htype;
    match Htype with
    | aexp_stack_sem (App_Stk _ (?a :: ?b :: nil)) ?fenv ?stk (?stk', ?n) =>
        let Mul := fresh "Mul" in
        pose proof (Mul := target_mult_aexp_wrapper stk a b);
        let Ha := fresh "Ha" in
        let Hb := fresh "Hb" in
        enough (Ha : exists v, aexp_stack_sem a fenv stk (stk, v));
        enough (Hb: exists v, aexp_stack_sem b fenv stk (stk, v))
    end.

  Ltac absstate_match_inversion' :=
    repeat match goal with
           | [ H: StackLogicGrammar.absstate_match_rel _ _ _ |- _ ] => invc H
           |[ H: StackLogicGrammar.meta_match_rel _ _ _ |- _ ] => invc H
           | [ H: eval_prop_rel _ _ |- _ ] => invc H
           | [ H: eval_prop_args_rel _ _ _ |- _ ] =>
               invc H
           | [ H: aexp_stack_sem (Var_Stk _)  _ _ _ |- _ ] =>
               invc H
           | [ H: aexp_stack_sem (Const_Stk _)  _ _ _ |- _ ] =>
               invc H
           | [ H: bexp_stack_sem _ _ _ _ |- _ ] =>
               invc H
           | [ H: nth_error _ _ = _ |- _ ] =>
               progress simpl in H; invc H
           end.

  
  Lemma stack_fact_env_valid:
    StackLogic.fact_env_valid
      SeriesTargetProgram.facts SeriesTargetProgram.fenv.
  Proof.
    unfold SeriesTargetProgram.facts, SeriesTargetProgram.fenv.
    unfold StackLogic.fact_env_valid. intros. simpl in H.
      destruct H as [ PQ1 | [ PQ2 | [ PQ3 | Invalid ]]]; [ .. | invs Invalid ].
    - invc PQ1.
      Arguments LTtoLEQProofCompilable.SC.CC.compile_aexp _ _%list_scope _%nat_scope/.
      simpl.
      Arguments StackLogic.aimpstk P Q fenv/.
      simpl. intros.
      invc H. invc H2.
      invc H1. do 7 make_stack_big_enough.
      absstate_match_inversion'.
      match goal with
      | [ |- StackLogicGrammar.absstate_match_rel _ _ (?a :: ?b :: ?c :: ?d :: ?e :: ?f :: ?g :: ?stk) ] =>
          rename a into x1, b into x2, c into x3, d into x4, e into x5, f into x6, g into x7
      end.
      rename x2 into rnn, x5 into rdn, x7 into x'n, x3 into i'n, x6 into dd'n.
      repeat match goal with | [ H: _ <= _ |- _ ] => clear H end.
      destruct H16 as (Eqrnn & Eqrdn & Eqi'n).
      destruct H13 as (Leqx'n & Eqx'n & Nonzerox1 & Eqdn & Nonzerodd'n & Eqdd).
      econstructor.
      + econstructor; simpl; lia.
      + econstructor; [ | repeat econstructor].
        econstructor.
        * repeat (econstructor; meta_smash).
        * simpl. repeat split; eauto.
          -- eapply first_implication_proof_arithmetic_proof; eauto.
          -- lia. 
          -- lia.
          -- lia.
    - invc PQ2. simpl. intros.
      invc H. invc H2. invc H1. do 7 make_stack_big_enough.
      absstate_match_inversion'.
      repeat match goal with
             | [ H: _ <= _ |- _ ] =>
                 clear H
             | [ H: _ /\ _ |- _ ] =>
                 destruct H
             | [ H: nth_error _ _ = Some _ |- _ ] => simpl in H; invc H
             end.
      unfold SeriesSourceProgram.dd, SeriesSourceProgram.x.
      invc H26.
      apply_target_mult_aexp_wrapper H14.
      destruct Ha, Hb. specialize (Mul _ _ H1 H7). aexp_stack_sem_same.
      invc DET.
      invc H7. invc H1. invc H15. clear Mul. clear H11 H10.
      
      apply_target_mult_aexp_wrapper H16.
      destruct Ha, Hb. specialize (Mul _ _ H1 H7).
      invc H1; invc H7. invc H17.
      aexp_stack_sem_same. invc DET. clear Mul. clear H11 H12.
      apply_target_mult_aexp_wrapper H27.
      destruct Ha, Hb. specialize (Mul _ _ H1 H7).
      invc H1. invc H7. invc H17.
      aexp_stack_sem_same.
      invc DET. clear Mul.
      unfold SeriesSourceProgram.x, SeriesSourceProgram.dd, SeriesSourceProgram.dn in *.
      repeat match goal with
      | [ H: _ <= _ |- _ ] => clear H
             end.
      all: try (eexists; meta_smash).
      econstructor; econstructor; [ .. | repeat econstructor].
      simpl. lia.
      econstructor. econstructor.
      eapply target_frac_add_numerator_wrapper.
      meta_smash. meta_smash. meta_smash. eapply target_exp_aexp_wrapper; meta_smash.
      econstructor.
      eapply target_frac_add_denominator_wrapper. meta_smash.
      eapply target_exp_aexp_wrapper; meta_smash.
      econstructor; meta_smash.
      econstructor; meta_smash.
      econstructor; meta_smash. econstructor.
      simpl.
      repeat split; eauto.
      * replace (x1 * 1) with (x1) by lia.
	replace x1 with (x1 + 0) at 1 by lia.
        replace x1 with (x1 + 0) at 2 by lia.
        eapply invariant_still_holds_proof_general; eauto.
      * lia.
    - invc PQ3. simpl. intros.
      invc H. invc H2.
      invc H1.
      do 7 make_stack_big_enough. clear H0.
      absstate_match_inversion'.
      repeat match goal with
             | [ H: _ <= _ |- _ ] => clear H
             end.
      invc H25.
      apply_target_mult_aexp_wrapper H7. destruct Ha, Hb. specialize (Mul _ _ H H0). aexp_stack_sem_same. invc DET. invc H. invc H13. clear H9. clear H6. clear Mul.
      invc H0.
      apply_target_mult_aexp_wrapper H10. destruct Ha, Hb. specialize (Mul _ _ H H0). aexp_stack_sem_same. invc DET. invc H. invc H13. invc H0. clear H6 H9. clear Mul.
      apply_target_mult_aexp_wrapper H26. destruct Ha, Hb. specialize (Mul _ _ H H0). invc H. invc H0. invc H13. clear H6 H9. aexp_stack_sem_same.
      invc DET. clear Mul. unfold SeriesSourceProgram.dd, SeriesSourceProgram.dn, SeriesSourceProgram.x in *.
      econstructor; econstructor; simpl; try lia; [ | repeat econstructor ].
      econstructor; meta_smash.
      symmetry in H27. eapply Nat.leb_gt in H27. lia.
      all: eexists; meta_smash.
  Qed.
  End SeriesActualProofCompilation.
End SeriesProofCompilationPluginOnly.
