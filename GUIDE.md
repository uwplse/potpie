## Claims

1. [The CC proof
   compiler](docs/Imp_LangTrick.ProofCompiler.ProofCompCodeCompAgnosticMod.html#CompilerAgnosticProofCompilerType.proof_compiler)
2. [The Tree proof compiler](docs/Imp_LangTrick.ProofCompiler.TreeProofCompiler.html#TreeProofCompiler)
3. [The "preserves stack" relation, `exp_stack_pure_rel`](docs/Imp_LangTrick.Stack.StackPurestBase.html#bexp_stack_pure_rel)
4. [The relation between Imp environments and Stack's stacks](docs/Imp_LangTrick.SpecCompiler.LogicTranslationBase.html#state_to_stack)
5. [The Tree
   plugin](docs/plugin)
6. [An example of the plugin being invoked](docs/plugin/theories/Hoarechecker.Demo.html)
7. [The implication database translation proof obligation](docs/Imp_LangTrick.ProofCompiler.ProofCompilableCodeCompiler.html#ValidImplicationTranslation.valid_imp_trans_def)
8. [The compiler that changes < to <= (and its associated proof compiler)](docs/Imp_LangTrick.CodeCompiler.EnvToStackLTtoLEQ.html#compile_bexp)
9. [The multiplication wrapper helper lemma from Section 4.1.1 in the paper](docs/Imp_LangTrick.Examples.rsa_impLang.html#mult_aexp_wrapper)
10. [The exponentiation wrapper helper lemma from Section 4.1.1 in the
    paper](docs/Imp_LangTrick.Examples.Exponentiation.html#exp_aexp_wrapper)
11. [The hoare triple for the infinite series example](docs/Imp_LangTrick.Examples.SeriesExample.html#series_hoare_triple)
12. [Soundness lemma for Tree](docs/Imp_LangTrick.ProofCompiler.TreeProofCompiler.html#TreeProofCompilerSound.tree_compiler_sound)
13. [The lemma that shows that `stk_valid_tree`, the certificate type,
    can be used to obtain `hl_stk`, the Stack Hoare proof type](docs/Imp_LangTrick.Stack.StkHoareTree.html#valid_tree_can_construct_hl_stk)
14. [The left shift case study, compiled with the incomplete compiler](docs/Imp_LangTrick.Examples.ExampleLeftShift_Incomplete.html)
15. [The max case study, compiled with the incorrect optimization compiler](docs/Imp_LangTrick.Examples.MaxIncorrectProofCompilationExample.html)
16. [The max case study, compiled with the unverified correct compiler](docs/Imp_LangTrick.Examples.MaxUnprovenCorrectProofCompilationExample.html)
17. [The min case study, which has to be compiled with the unverified
    correct compiler](docs/Imp_LangTrick.Examples.MinProofCompilationExample.html)
18. [The incomplete proof compiler (from our PotPie 3 Ways)](docs/Imp_LangTrick.Examples.ProofCompilers.IncompleteProofCompiler.html)
19. [The incorrect proof compiler (from the PotPie 3 Ways section)](docs/Imp_LangTrick.Examples.ProofCompilers.BuggyProofCompiler.html)
20. [The unverified correct proof compiler](docs/Imp_LangTrick.Examples.ProofCompilers.UnprovenCorrectProofCompiler.html)
21. [The certificate generator in the Tree plugin](https://github.com/uwplse/potpie/tree/v0.4/plugin/src/checker.ml#L81)
22. [`stk_valid_tree`, the certificate type](docs/Imp_LangTrick.Stack.StkHoareTree.html#stk_valid_tree)
23. [How the plugin's boolean tree checker determines that all of the
    functions preserve the stack](docs/Imp_LangTrick.Stack.FuncsFrame.html#funcs_frame)
24. [The plugin's boolean tree checker](docs/plugin/hoarechecker/Hoarechecker_plugin/BoolChecker/index.html)
25. [Uniqueness of Identity Proofs (UIP) for `AbsEnv`, the type of
    assertions for
    Imp](docs/Imp_LangTrick.Imp.Imp_LangLogPropDec.html#UIP_AbsEnv):
    note that this also lets us get UIP for the implication database
    for Imp, since UIP for a type `T` implies UIP for `T * T` pairs,
    and UIP for a type `A` implies UIP for `list A`.
26. [UIP for Imp's function environments](docs/Imp_LangTrick.ProofCompiler.ProofCompilerHelpers.html#UIP_fun_env_refl)
27. [An example of setting opaques for the plugin's normalization
    algorithm](https://github.com/uwplse/potpie/tree/v0.4/plugin/theories/Demo.v#L49):
    this led to 100x speedup for the certificate generator!
28. [Proof compiler
    automation, which helps with satisfying proof obligations for both
	Tree and CC](docs/Imp_LangTrick.ProofCompiler.ProofCompAuto.html)
29. [Semantics proof automation, which also helps with proof obligations](docs/Imp_LangTrick.Tactics.SemanTactics.html)
30. [Sound translation of a Hoare triple's precondition, one of our
    proof obligations](docs/Imp_LangTrick.ProofCompiler.ProofCompCodeCompAgnosticMod.html#ProgramProofCompilationType.pre_sound)
31. [Sound translation of a Hoare triple's postcondition, another one
    of our proof obligations](docs/Imp_LangTrick.ProofCompiler.ProofCompCodeCompAgnosticMod.html#ProgramProofCompilationType.post_sound)
32. [Utilizing unification with Coq's options to avoid unnecessary
    normalization calls](https://github.com/uwplse/potpie/tree/v0.4/plugin/src/CoqCoreInductives.ml#L54)
