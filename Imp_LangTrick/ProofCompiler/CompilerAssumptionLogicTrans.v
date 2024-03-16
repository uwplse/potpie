From Coq Require Import String List Peano Arith Program.Equality Nat
Psatz Arith.PeanoNat Program.Equality.

From Imp_LangTrick Require Import StackLogic Imp_LangLogHoare Imp_LangTrickLanguage EnvToStack StackLanguage Imp_LangLogProp LogicProp StackLangTheorems StackLogicBase.
From Imp_LangTrick Require Import LogicTranslationBackwards StackLogicBase TranslationPure LogicTranslationAdequate LogicTrans.
From Imp_LangTrick Require Export ProofSubstitution ImpVarMapTheorems Imp_LangLogSubstAdequate.
From Imp_LangTrick Require Import Imp_LangImpHigherOrderRel Imp_LangImpHigherOrderRelTheorems CompilerCorrect StackFrame1
StackExtensionDeterministic FunctionWellFormed LogicTranslationBase ParamsWellFormed
Imp_LangLogSubst.

(*
 * 
 *)

Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope imp_langtrick_scope.
Print a_Imp_Lang. 

Definition aexp_args_wf_map (map : list ident) :=
  prop_args_rel (V := nat) (var_map_wf_wrt_aexp map). 

Definition bexp_args_wf_map (map : list ident) :=
  prop_args_rel (V := bool) (var_map_wf_wrt_bexp map). 

Definition lp_arith_wf_map map :=
  prop_rel (V := nat) (var_map_wf_wrt_aexp map). 
  
Definition lp_bool_wf_map map :=
  prop_rel (V := bool) (var_map_wf_wrt_bexp map). 

Definition lp_Imp_Lang_wf_map map :=
  Imp_Lang_lp_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map). 

Definition log_Imp_Lang_wf_map map := 
  AbsEnv_prop_rel (var_map_wf_wrt_aexp map) (var_map_wf_wrt_bexp map). 

Definition aexp_args_wf func_list fenv :=
  prop_args_rel (V := nat) (FunctionWellFormed.fun_app_well_formed fenv func_list). 

Definition bexp_args_wf func_list fenv :=
  prop_args_rel (V := bool) (FunctionWellFormed.fun_app_bexp_well_formed fenv func_list). 

Definition lp_arith_wf func_list fenv :=
  prop_rel (V := nat) (FunctionWellFormed.fun_app_well_formed fenv func_list). 

Definition lp_bool_wf func_list fenv :=
  prop_rel (V := bool) (FunctionWellFormed.fun_app_bexp_well_formed fenv func_list).

Definition lp_Imp_Lang_wf func_list fenv :=
  Imp_Lang_lp_prop_rel (FunctionWellFormed.fun_app_well_formed fenv func_list) (FunctionWellFormed.fun_app_bexp_well_formed fenv func_list).

Definition log_Imp_Lang_wf func_list fenv :=
  AbsEnv_prop_rel (FunctionWellFormed.fun_app_well_formed fenv func_list) (FunctionWellFormed.fun_app_bexp_well_formed fenv func_list).