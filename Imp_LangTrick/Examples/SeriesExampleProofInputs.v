From Coq Require Import List String Arith Psatz.


From Imp_LangTrick Require Import Imp_LangTrickLanguage StackLanguage FactEnvTranslator ProofCompAuto TerminatesForSure ProofCompCodeCompAgnosticMod ProofCompAutoAnother.
From Imp_LangTrick Require Import StackLangTheorems ImpVarMap ProofCompilerBase Imp_LangLogProp LogicProp ProofCompilerHelpers Imp_LangHoareWF Imp_LangLogHoare ProofCompilerPostHelpers FunctionWellFormed ParamsWellFormed TranslationPure.
From Imp_LangTrick Require Import SeriesExample.
From Imp_LangTrick Require Import EnvToStackLTtoLEQ.

Module Type SeriesProgramInputs.
  Parameter x : nat.  (* \sum_{i=1}^\infty x^{-i} *)
  Parameter dn : nat. (* The _d_elta _n_umerator *)
  Parameter dd : nat. (* The _d_elta _d_enominator *)
End SeriesProgramInputs.

Fixpoint stk_fenv_ify (funs : list fun_stk) : fun_env_stk :=
  match funs with
  | nil => init_fenv_stk
  | f :: funs' =>
      update (Name f) f (stk_fenv_ify funs')
  end.

(* Module SeriesProofCompilationInputs(S: SeriesProgramInputs). *)

(*   Module SeriesSourceProgram <: ProofCompMod.SourceProgramType. *)
(*     Include S. *)
(*     Definition program := series_calculation_program x dn dd. *)
(*     Definition precond := series_precond x dn dd. *)
(*     Definition postcond := series_postcond x dn dd. *)
(*     Definition fenv := series_fenv. *)
(*     Definition facts := series_program_facts x dn dd. *)
(*     Definition hoare_triple := series_hoare_triple x dn dd. *)
(*     Definition idents := construct_trans program. *)
(*     Definition num_args := 0. *)
(*     Definition funcs := series_funcs. *)
(*   End SeriesSourceProgram. *)

(*   Fixpoint stk_fenv_ify (funs : list fun_stk) : fun_env_stk := *)
(*     match funs with *)
(*     | nil => init_fenv_stk *)
(*     | f :: funs' => *)
(*         update (Name f) f (stk_fenv_ify funs') *)
(*     end. *)

(*   Module SeriesTargetProgramInputs <: TargetProgramInputs. *)
(*     Definition target_fenv : fun_env_stk := stk_fenv_ify (map compile_function SeriesSourceProgram.funcs). *)
(*     Definition target_facts idents args : StackLogic.implication_env_stk := *)
(*       map (fun (x: (AbsEnv * AbsEnv)) => *)
(*              let (P, Q) := x in *)
(*              (LTtoLEQCompilerAgnostic.SC.comp_logic args idents P, LTtoLEQCompilerAgnostic.SC.comp_logic args idents Q)) *)
(*           SeriesSourceProgram.facts. *)
(*   End SeriesTargetProgramInputs. *)

(* Module SeriesTargetProgram := CompilerAgnosticProofCompilableTargetProgram (SeriesSourceProgram) (LTtoLEQCompilerAgnostic.PC.CC) (LTtoLEQCompilerAgnostic.PC.SC) (SeriesTargetProgramInputs). *)
(* End SeriesProofCompilationInputs. *)
