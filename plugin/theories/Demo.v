From Hoarechecker Require Import Loader.
Require Import Coq.Program.Tactics.
From Coq Require Import String List ZArith.
From Imp_LangTrick Require Import StkHoareTree StackLogicGrammar LogicProp StackLanguage PluginHelpers StateUpdateReflection StackLogic StackIncreaseAdequacy StackIncrease StackPurestBaseReflection SeriesHelperCompilation TreeCompilationExample FuncsFrame StackFrameBase StackFrameReflection.


Local Open Scope string_scope.
Local Open Scope list_scope.

Definition abstruetrue := BaseState AbsStkTrue (MetaBool (TrueProp _ _ )).
Definition abstrue := BaseState (AbsStkSize 3) (MetaBool (TrueProp _ _ )).

Definition absand1 := Eval compute in (AbsAnd abstrue abstruetrue).
Definition absand2 := Eval compute in (AbsAnd abstrue abstrue).

Definition add_1_2 := Plus_Stk (Const_Stk 1) (Const_Stk 2).
Definition assign_2_add_1_2 := Assign_Stk 2 add_1_2.


Definition my_tree := StkHTAssign abstrue 2 add_1_2.
Definition my_seq := Seq_Stk assign_2_add_1_2 assign_2_add_1_2.

Definition seq_tree := StkHTSeq abstrue abstrue abstrue assign_2_add_1_2 assign_2_add_1_2 my_tree my_tree.

Definition push := Push_Stk.
Definition push_tree := StkHTPush abstrue.
Definition my_if := If_Stk True_Stk assign_2_add_1_2 assign_2_add_1_2.
Definition if_tree := StkHTIf abstrue abstrue True_Stk assign_2_add_1_2 my_seq my_tree seq_tree.

Definition simple_fun := Eval compute in (init_fenv_stk "id").

Definition my_facts_env: implication_env_stk := nil.

Definition roc_example := StkHTCon (absand1, absand2) (absand2, absand2) (Skip_Stk) (StkHTSkip absand2).

(* MyDebug (fun x => match x with *)
(*                | Some a => Some (Imp_LangTrick.Stack.StackExprWellFormed.construct_aexp_well_formed a) *)
(*                | None => None *)
(*                end). *)

(* MyDebug SourceProd.facts. *)


Set HoareChecker Certify.

(* Avoid unfolding these at normalization time.
   Makes things faster and makes the generated certificate more readable.
   We can definitely add more functions here, just not sure what is relevant yet. *)
Configure HoareChecker { opaque
  nth_error nth_default nth
  Nat.mul Nat.add Nat.sub Nat.pow
  Z.of_nat Z.pow Z.add Z.mul Z.sub
}.

Time Certify my_tree init_fenv_stk my_facts_env empty_facts_valid nil as bar.

Check bar.

Time Certify seq_tree init_fenv_stk my_facts_env empty_facts_valid nil as baz.

Check baz.

Time Certify roc_example init_fenv_stk my_facts_env empty_facts_valid nil as foo.

Check foo.

(* Should take less than a second now! *)
Time Certify (ProdTargetTree.tree) (ProdTargetTree.fenv) (ProdTargetTree.facts) (ProdValidFacts.valid_facts) (ProdTargetTree.funcs) as prod.

Check prod.

(* Down from 800 seconds to 0.275 seconds hahaha *)
Time Certify (ExpTargetTree.tree) (ExpTargetTree.fenv) (ExpTargetTree.facts) (ExpValidFacts.valid_facts) (ExpTargetTree.funcs) as exp.

Check exp.

(* Time Certify (SqrtTargetTree.tree) (SqrtTargetTree.fenv) (SqrtTargetTree.facts) (SqrtTargetFacts.valid_facts) (SqrtTargetTree.funcs) as sqrt. *)

(* Check sqrt. *)

(* Time Certify (SeriesTargetTree.tree) (SeriesTargetTree.fenv) (SeriesTargetTree.facts) (SeriesTargetFacts.valid_facts) (SeriesTargetTree.funcs) as series. *)

(* Check series. *)

Time Certify (LShiftTargetTree.tree) (LShiftTargetTree.fenv) (LShiftTargetTree.facts) (LShiftTargetFacts.valid_facts) (LShiftTargetTree.funcs) as lshift.

Check lshift.

Unset HoareChecker Certify.

Time Certify (MaxTargetTree.tree) (MaxTargetTree.fenv) (MaxTargetTree.facts) (MaxTargetFacts.valid_facts) (MaxTargetTree.funcs) as maxincomplete.

Print maxincomplete.

Time Certify (MaxTargetTreeCorrect.tree) (MaxTargetTreeCorrect.fenv) (MaxTargetTreeCorrect.facts) (MaxTargetFactsCorrect.valid_facts) (MaxTargetTreeCorrect.funcs) as maxcorrect.

Print maxcorrect.





