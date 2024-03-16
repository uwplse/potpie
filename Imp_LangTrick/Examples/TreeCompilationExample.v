From Imp_LangTrick.Examples Require Import SeriesHelperCompilation SquareRoot SeriesExampleProofInputs SeriesExample SeriesExampleProofCompiled.
From Imp_LangTrick.Imp Require Import Imp_LangTrickLanguage HoareTree.
From Imp_LangTrick.Stack Require Import StackLanguage StkHoareTree.
From Imp_LangTrick.ProofCompiler Require Import TreeProofCompiler.

From Imp_LangTrick.CodeCompiler Require Import EnvToStackLTtoLEQ.
From Imp_LangTrick.ProofCompiler Require Import ProofCompMod ProofCompCodeCompAgnosticMod ProofCompilableCodeCompiler.
From Imp_LangTrick Require Import BuggyProofCompiler MaxIncorrectProofCompilationExample IncompleteProofCompiler ExampleLeftShift_Incomplete UnprovenCorrectProofCompiler. 

From Coq Require Import List String Arith.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope nat_scope.

Module LTtoLEQTreeCompiler := TreeProofCompiler (LTtoLEQProofCompilable.CC) (LTtoLEQProofCompilable.SC).

Module Type SourceProgramTree (SPT : SourceProgramType).
  Include SPT.
  Parameter tree: imp_hoare_tree.
End SourceProgramTree.

Module MakeSourceProgramTree(SPT : SourceProgramType) <: SourceProgramTree(SPT).
  Include SPT.
  Definition tree := imp_tree_constructor (SPT.precond) (SPT.program) (SPT.postcond) (SPT.fenv) (SPT.facts) (SPT.hoare_triple).
End MakeSourceProgramTree.
  

Module SourceProdTree := MakeSourceProgramTree(SourceProd).

Module Type TargetProgramTree (TPT: TargetProgramType).
  Include TPT.
  Parameter tree : stk_hoare_tree.
End TargetProgramTree.

Module GetStackFactsValid (PPC : ProgramProofCompilationType).
  Lemma valid_facts :
    StackLogic.fact_env_valid PPC.TARGET.facts PPC.TARGET.fenv.
  Proof.
    pose proof (PPC.implication_transformer).
    unfold PPC.CAPC.PC.valid_imp_trans_def in H.
    destruct H as (_ & _ & S).
    eauto.
  Defined.
End GetStackFactsValid.
  
Module Type FenvCompiler. 
  Parameter FenvCompilerInstantiated : (ident -> fun_Imp_Lang) -> (fun_env_stk). 
End FenvCompiler.

Module TargetProgramInputsFunctor (CAPC : CompilerAgnosticProofCompilerType) (FC : FenvCompiler) (SPT : SourceProgramType) <: TargetProgramInputs. 
  Definition target_fenv := FC.FenvCompilerInstantiated SPT.fenv.
  Definition target_facts := 
    fun idents => fun args => map (fun pq =>
      match pq with
      |(P, Q) => ((CAPC.SC.comp_logic args idents P), (CAPC.SC.comp_logic args idents Q))
      end) SPT.facts.
End TargetProgramInputsFunctor.


Module CompileTree (SPT: SourceProgramType) (CAPC : CompilerAgnosticProofCompilerType) (FC : FenvCompiler). (* <: TargetProgramTree *) (* I don't know why coq doesn't like this *)
  Module TPI := TargetProgramInputsFunctor (CAPC) (FC) (SPT). 
  Module ST := MakeSourceProgramTree (SPT).
  Module TPT := CompilerAgnosticProofCompilableTargetProgram(SPT)(CAPC.CC)(CAPC.SC)(TPI).
  Include TPT.
  Module TC := TreeProofCompiler (CAPC.PC.CC) (CAPC.PC.SC).
  Definition tree := TC.tree_proof_compiler SPT.num_args SPT.idents ST.tree.
  Definition funcs := map compile_function (SPT.funcs).

  Ltac try_unfold :=
    try unfold SPT.num_args;
    try unfold SPT.idents;
    try unfold ST.tree;
    try unfold program;
    try unfold precond;
    try unfold postcond;
    try unfold fenv;
    try unfold facts.
End CompileTree.

Module ProdTargetFenvCompiler <: FenvCompiler.
  Definition FenvCompilerInstantiated := EnvToStackLTtoLEQ.compile_fenv.
End ProdTargetFenvCompiler. 

Module ProdTargetTree := CompileTree(SourceProd) (LTtoLEQCompilerAgnostic) (ProdTargetFenvCompiler).
Module ProdValidFacts := GetStackFactsValid(CompileProd).

Definition stk_prod_tree := Eval compute in (ProdTargetTree.tree).

Module ExpTargetTree := CompileTree(SourceExp) (LTtoLEQCompilerAgnostic) (ProdTargetFenvCompiler).
Module ExpValidFacts := GetStackFactsValid(CompileExp).

Definition stk_exp_tree := Eval compute in ExpTargetTree.tree.

(* Change these constants to arrive at whatever precision you like *)
Module SqrtInputs <: SqrtProgramInputs. 
  Definition a := 5. 
  Definition b := 10. 
  Definition epsilon_n := 6.
  Definition epsilon_d := 12.
End SqrtInputs. 

Module InstantiatedSqrtProofCompilation := SquareRootProofCompilation(SqrtInputs). 


Module SqrtTargetTree := CompileTree (InstantiatedSqrtProofCompilation.SqrtSource) (LTtoLEQCompilerAgnostic) (ProdTargetFenvCompiler).
Module SqrtTargetFacts := GetStackFactsValid(InstantiatedSqrtProofCompilation.ProofCompileSquareRoot).
Definition stk_sqrt_tree := Eval compute in SqrtTargetTree.tree.
Check stk_sqrt_tree.

Module SeriesInputs <: SeriesProgramInputs. 
  Definition x := 5. 
  Definition dn := 6.
  Definition dd := 12.
End SeriesInputs. 

Module SeriesInstantiatedProofCompilation := SeriesProofCompilation (SeriesInputs). 

Module SeriesTargetTree := CompileTree (SeriesInstantiatedProofCompilation.SeriesSourceProgram) (LTtoLEQCompilerAgnostic) (ProdTargetFenvCompiler). 
Module SeriesTargetFacts := GetStackFactsValid (SeriesInstantiatedProofCompilation.SeriesActualProofCompilation2). 
Definition stk_series_tree := Eval compute in SeriesTargetTree.tree.

Module MaxFenvCompiler <: FenvCompiler.
  Definition FenvCompilerInstantiated := EnvToStackBuggy.compile_fenv.
End MaxFenvCompiler.
Module MaxTargetInputs := TargetProgramInputsFunctor (BuggyProofCompiler) (MaxFenvCompiler) (IncorrectlyCompiledFenvExample_ModuleVersion.SourceAssignMax).
Module MaxTargetTree := CompileTree (IncorrectlyCompiledFenvExample_ModuleVersion.SourceAssignMax) (BuggyProofCompiler) (MaxFenvCompiler).
Module MaxTargetFacts := GetStackFactsValid (IncorrectlyCompiledFenvExample_ModuleVersion.CompileMaxProofs). 
Definition stk_max_tree := Eval compute in MaxTargetTree.tree.

Module LShiftFenvCompiler <: FenvCompiler. 
  Definition FenvCompilerInstantiated := EnvToStackIncomplete.compile_fenv_incomplete.
End LShiftFenvCompiler.
Module LShiftTargetInputs := TargetProgramInputsFunctor (IncompleteProofCompiler) (LShiftFenvCompiler).
Module LShiftTargetTree := CompileTree (SourceAssignLeftShift) (IncompleteProofCompiler) (LShiftFenvCompiler). 
Module LShiftTargetFacts := GetStackFactsValid (CompileLeftShiftIncomplete). 
Definition stk_lshift_tree := Eval compute in LShiftTargetTree.tree.

Require Import MaxUnprovenCorrectProofCompilationExample. 

Module MaxFenvCorrectCompiler <: FenvCompiler.
  Definition FenvCompilerInstantiated := EnvToStack.compile_fenv.
End MaxFenvCorrectCompiler.
Module MaxTargetInputsCorrect := TargetProgramInputsFunctor (UnprovenCorrectProofCompiler) (MaxFenvCorrectCompiler) (MaxUnprovenCorrectProofCompilationExample.CorrectlyCompiledFenvExample_ModuleVersion.SourceAssignMax).
Module MaxTargetTreeCorrect := CompileTree (MaxUnprovenCorrectProofCompilationExample.CorrectlyCompiledFenvExample_ModuleVersion.SourceAssignMax) (UnprovenCorrectProofCompiler) (MaxFenvCorrectCompiler).
Module MaxTargetFactsCorrect := GetStackFactsValid (CorrectlyCompiledFenvExample_ModuleVersion.CompileMaxProofs). 
Definition stk_max_correct_tree := Eval compute in MaxTargetTree.tree.
