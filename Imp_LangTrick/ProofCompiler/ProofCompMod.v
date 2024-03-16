From Coq Require Import List Arith String Program.Equality.
From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage StackLangTheorems ProofCompiler.
From Imp_LangTrick Require Import Imp_LangLogSubst Imp_LangLogProp Imp_LangLogHoare StackLogic.
From Imp_LangTrick Require Import LogicTranslationBase EnvToStack LogicProp ProofCompilerHelpers ProofCompilerPostHelpers Imp_LangImpHigherOrderRel Imp_LangHoareWF LogicTranslationAdequate FunctionWellFormed ParamsWellFormed CompilerAssumptionLogicTrans TranslationPure FactEnvTranslator.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.

Definition translate_AbsEnv_pair idents n_args PQ (comp_logic : nat -> list ident -> AbsEnv -> AbsState) :=
  match PQ with
  | (P, Q) => ((comp_logic n_args idents P), comp_logic n_args idents Q)
  end.

Module Type SourceProgramType.
  Parameter program: imp_Imp_Lang.
  Parameter precond postcond: AbsEnv.
  Parameter fenv: fun_env.
  Parameter facts: implication_env.
  Parameter hoare_triple: hl_Imp_Lang precond program postcond facts fenv.
  Parameter idents: list ident.
  Parameter num_args: nat.
  Parameter funcs: list fun_Imp_Lang.

End SourceProgramType.

Module Type TargetProgramType.
  Declare Module SP : SourceProgramType.
  Parameter compile_imp_lang_log: AbsEnv -> AbsState.
  Parameter program: imp_stack.
  Parameter precond postcond: AbsState.
  Parameter fenv: fun_env_stk.
  Parameter facts: implication_env_stk.
End TargetProgramType.