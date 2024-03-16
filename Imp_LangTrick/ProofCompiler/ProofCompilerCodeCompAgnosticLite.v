From Coq Require Import String List Peano Arith Program.Equality.
From Imp_LangTrick Require Import StackLogic Imp_LangLogHoare Imp_LangTrickLanguage EnvToStack StackLanguage Imp_LangLogProp LogicProp StackLangTheorems StackLogicBase.
From Imp_LangTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From Imp_LangTrick Require Export ProofSubstitution ImpVarMapTheorems Imp_LangLogSubstAdequate.
From Imp_LangTrick Require Import Imp_LangImpHigherOrderRel ProofCompilerHelpers Imp_LangHoareWF.
From Imp_LangTrick Require Import ProofCompilerBase Imp_LangImpHigherOrderRelTheorems.
From Imp_LangTrick Require Import FunctionWellFormed
CompilerAssumptionLogicTrans.
From Imp_LangTrick Require Import Imp_LangLogicHelpers FactEnvTranslator.
From Imp_LangTrick Require Import ProofCompilableCodeCompiler.

(*
 * This is the file for the proof compiler, which compiles
 * proofs in Imp_LangTrickLogic to proofs in StackLogic.
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.