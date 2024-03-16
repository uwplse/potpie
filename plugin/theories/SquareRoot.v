From Hoarechecker Require Import Loader.
From Coq Require Import String List ZArith.
From Imp_LangTrick Require Import StkHoareTree StackLogicGrammar LogicProp StackLanguage PluginHelpers StateUpdateReflection StackLogic StackIncreaseAdequacy StackIncrease StackPurestBaseReflection SeriesHelperCompilation TreeCompilationExample FuncsFrame StackFrameBase StackFrameReflection.

Configure HoareChecker { opaque
  nth_error nth_default nth
  Nat.mul Nat.add Nat.sub Nat.pow
  Z.of_nat Z.pow Z.add Z.mul Z.sub
    }.

Set HoareChecker Certify.

Time Certify (SqrtTargetTree.tree) (SqrtTargetTree.fenv) (SqrtTargetTree.facts) (SqrtTargetFacts.valid_facts) (SqrtTargetTree.funcs) as sqrt.

Check sqrt.
