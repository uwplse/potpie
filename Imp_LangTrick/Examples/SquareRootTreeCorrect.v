From Coq Require Import Psatz Arith String List ZArith.
From Coq Require Import QArith_base.
From Imp_LangTrick Require Import StackLanguage Imp_LangTrickLanguage Base rsa_impLang.
From Imp_LangTrick Require Import ImpExampleHelpers ProofCompAutoAnother.
From Imp_LangTrick Require Import StackLangTheorems Imp_LangLogProp LogicProp.
From Imp_LangTrick Require Import Imp_LangLogHoare ProofCompMod SeriesExample ProofCompilableCodeCompiler EnvToStackLTtoLEQ ProofCompCodeCompAgnosticMod NotTerribleBImpLangInversion StackLanguage SeriesHelperCompilation.

From Imp_LangTrick.Tactics Require Import SemanTactics MiscTactics.
From Imp_LangTrick Require Import SquareRootCore.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nat_scope.

Require Import FunctionWellFormed TranslationPure ParamsWellFormed ProofCompilerHelpers Imp_LangImpHigherOrderRel Imp_LangHoareWF CompilerAssumptionLogicTrans AimpWfAndCheckProofAuto ProofCompAuto HelperWrappers SquareRootTreeCompiled.

Module SquareRootTreeCorrect(S: SqrtProgramInputs).
  Module SQRTTPC := SquareRootTreeProofCompilation(S).
  Include SQRTTPC.
  Include TreeProofCompileSquareRoot.

  Lemma pre_sound : CAPC.SC.transrelation_sound SOURCE.precond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    econstructor. intros. split; intros.
    - simpl. destruct_stks stk. meta_smash.
      + unfold SOURCE.num_args in H. simpl. lia.
      + unfold SOURCE.precond, sqrt_precond in H1. 
        invc H1. invc H3. invc H2. intuition.
    (* + repeat econstructor. *)
    - invc H1. invc H4. invc H7. invc H3. repeat econstructor; intuition.
  Qed.

  Lemma post_sound : CAPC.SC.transrelation_sound SOURCE.postcond SOURCE.fenv TARGET.fenv SOURCE.idents SOURCE.num_args.
  Proof.
    econstructor. intros. split; intros.
    - simpl. destruct_stks stk. meta_smash.
      + unfold SOURCE.num_args in H. simpl. lia.
      + unfold SOURCE.postcond, sqrt_postcond in H1.
        unfold sqrt_postcond_prop.  
        invc H1. invc H3. invc H2. invc H6. invc H7.
        unfold sqrt_postcond_prop in H8. 
        intuition.
      + repeat econstructor.
    - invc H1. invc H4. invc H7. invc H3. invc H4. invc H8. invc H9. 
      destruct_stks stk. 
      simpl in H13, H15. invs H13. invs H15.
      econstructor. econstructor. econstructor. econstructor. reflexivity. econstructor. reflexivity.
      assumption.       
  Qed.
End SquareRootTreeCorrect.

