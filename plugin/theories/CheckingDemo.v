From Hoarechecker Require Import Loader.
Require Import Coq.Program.Tactics.
From Coq Require Import String List ZArith.
From Imp_LangTrick Require Import StkHoareTree StackLogicGrammar LogicProp StackLanguage PluginHelpers StateUpdateReflection StackLogic StackIncreaseAdequacy StackIncrease StackPurestBaseReflection SeriesHelperCompilation TreeCompilationExample FuncsFrame StackFrameBase StackFrameReflection.

Unset HoareChecker Certify.

(* Avoid unfolding these at normalization time.
   Makes things faster and makes the generated certificate more readable.
   We can definitely add more functions here, just not sure what is relevant yet. *)
Configure HoareChecker { opaque
  nth_error nth_default nth
  Nat.mul Nat.add Nat.sub Nat.pow
  Z.of_nat Z.pow Z.add Z.mul Z.sub
}.


(* Should take less than a second now! *)
Time Certify (ProdTargetTree.tree) (ProdTargetTree.fenv) (ProdTargetTree.facts) (ProdValidFacts.valid_facts) (ProdTargetTree.funcs) as prod.

Print prod.

Time Certify (ExpTargetTree.tree) (ExpTargetTree.fenv) (ExpTargetTree.facts) (ExpValidFacts.valid_facts) (ExpTargetTree.funcs) as exp.

Print exp.

Time Certify (SqrtTargetTree.tree) (SqrtTargetTree.fenv) (SqrtTargetTree.facts) (SqrtTargetFacts.valid_facts) (SqrtTargetTree.funcs) as sqrt.

Print sqrt.

Time Certify (SeriesTargetTree.tree) (SeriesTargetTree.fenv) (SeriesTargetTree.facts) (SeriesTargetFacts.valid_facts) (SeriesTargetTree.funcs) as series.

Print series.

Time Certify (LShiftTargetTree.tree) (LShiftTargetTree.fenv) (LShiftTargetTree.facts) (LShiftTargetFacts.valid_facts) (LShiftTargetTree.funcs) as lshift.

Print lshift.
