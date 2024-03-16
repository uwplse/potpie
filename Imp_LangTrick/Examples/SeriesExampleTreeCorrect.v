From Coq Require Import List String Arith Psatz.


From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage FactEnvTranslator ProofCompAuto TerminatesForSure ProofCompCodeCompAgnosticMod ProofCompAutoAnother.
From Imp_LangTrick Require Import StackLangTheorems ImpVarMap ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed TranslationPure Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems.
From Imp_LangTrick Require Import SeriesExampleProofInputs.
From Imp_LangTrick Require Import EnvToStackLTtoLEQ.
From Imp_LangTrick Require Import SeriesExample.
From Imp_LangTrick Require Import SeriesHelperCompilation.
From Imp_LangTrick.Tactics Require Import MiscTactics.
From Imp_LangTrick Require Import StackFrameReflection StackPurestBaseReflection HelperWrappers SeriesExampleTreeProofCompiled.
Local Open Scope string_scope.



Module SeriesTreeCorrect(S: SeriesProgramInputs).
  Module SPCPO := SeriesProofCompilationPluginOnly(S).
  Include SPCPO.
  Include SeriesActualProofCompilation.

  
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
End SeriesTreeCorrect.
