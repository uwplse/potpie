From Coq Require Import String Arith Psatz Bool List Program.Equality Lists.ListSet .
From Imp_LangTrick Require Import Imp_LangTrickLanguage Imp_LangLogProp Imp_LangLogicHelpers StackLanguage EnvToStack StackLogicGrammar LogicProp.

Inductive state_to_stack : 
  (list ident) ->
  nat_env ->
  (list nat) ->
  (list nat) -> 
  Prop := 
  | State_trans : 
    forall map nenv dbenv,
    state_to_stack map nenv dbenv ((List.map nenv map) ++ dbenv).
