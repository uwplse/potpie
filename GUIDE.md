## Claims

1. [The CC proof
   compiler](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/ProofCompiler/ProofCompCodeCompAgnosticMod.v#L33)
2. [The Tree proof compiler](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/ProofCompiler/TreeProofCompiler.v#L15)
3. [The "preserves stack" relation, `exp_stack_pure_rel`](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Stack/StackPurestBase.v#L27)
4. [The relation between Imp environments and Stack's stacks](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/SpecCompiler/LogicTranslationBase.v#L4)
5. [The Tree
   plugin](https://github.com/uwplse/potpie/tree/v0.4/plugin/src/)
6. [An example of the plugin being invoked](https://github.com/uwplse/potpie/tree/v0.4/plugin/theories/Demo.v#L55)
7. [The implication database translation proof obligation](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/ProofCompiler/ProofCompilableCodeCompiler.v#L714)
8. [The compiler that changes < to <= (and its associated proof compiler)](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/CodeCompiler/EnvToStackLTtoLEQ.v#L41)
9. [The multiplication wrapper helper lemma from Section <>](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Examples/rsa_impLang.v#L160)
10. [The exponentiation wrapper helper lemma from Section <>](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Examples/Exponentiation.v#L253)
11. [The hoare triple for the infinite series example](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Examples/SeriesExample.v#L705)
12. [Soundness lemma for Tree](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/ProofCompiler/TreeProofCompiler.v#L70)
13. [The lemma that shows that `stk_valid_tree`, the certificate type,
    can be used to obtain `hl_stk`, the Stack Hoare proof type](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Stack/StkHoareTree.v#L218)
14. [The left shift case study, compiled with the incomplete compiler](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Examples/ExampleLeftShift_Incomplete.v)
15. [The max case study, compiled with the incorrect optimization compiler](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Examples/MaxIncorrectProofCompilationExample.v)
16. [The max case study, compiled with the unverified correct compiler](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Examples/MaxUnprovenCorrectProofCompilationExample.v)
17. [The min case study, which has to be compiled with the unverified
    correct compiler](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Examples/MinProofCompilationExample.v)
18. [The incomplete proof compiler (from our PotPie 3 Ways)](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Examples/ProofCompilers/IncompleteProofCompiler.v)
19. [The incorrect proof compiler (from the PotPie 3 Ways section)](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Examples/ProofCompilers/BuggyProofCompiler.v)
20. [The unverified correct proof compiler](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Examples/ProofCompilers/UnprovenCorrectProofCompiler.v)
21. [The certificate generator in the Tree plugin](https://github.com/uwplse/potpie/tree/v0.4/plugin/src/checker.ml#L81)
22. [`stk_valid_tree`, the certificate type](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Stack/StkHoareTree.v#L61)
23. [How the plugin's boolean tree checker determines that all of the
    functions preserve the stack](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Stack/FuncsFrame.v#L133)
24. [The plugin's boolean tree checker](https://github.com/uwplse/potpie/tree/v0.4/plugin/src/boolChecker.ml#L)
25. [Uniqueness of Identity Proofs (UIP) for `AbsEnv`, the type of
    assertions for
    Imp](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Imp/Imp_LangLogPropDec.v#L19):
    note that this also lets us get UIP for the implication database
    for Imp, since UIP for a type `T` implies UIP for `T * T` pairs,
    and UIP for a type `A` implies UIP for `list A`.
26. [UIP for Imp's function environments](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/ProofCompiler/ProofCompilerHelpers.v#L100)
27. [An example of setting opaques for the plugin's normalization
    algorithm](https://github.com/uwplse/potpie/tree/v0.4/plugin/theories/Demo.v#L49):
    this led to 100x speedup for the certificate generator!
28. [Proof compiler
    automation, which helps with satisfying proof obligations for both
	Tree and CC](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/ProofCompiler/ProofCompAuto.v)
29. [Semantics proof automation, which also helps with proof obligations](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/Tactics/SemanTactics.v)
30. [Sound translation of a Hoare triple's precondition, one of our
    proof obligations](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/ProofCompiler/ProofCompCodeCompAgnosticMod.v#L68)
31. [Sound translation of a Hoare triple's postcondition, another one
    of our proof obligations](https://github.com/uwplse/potpie/tree/v0.4/Imp_LangTrick/ProofCompiler/ProofCompCodeCompAgnosticMod.v#L69)
32. [Utilizing unification with Coq's options to avoid unnecessary
    normalization calls](https://github.com/uwplse/potpie/tree/v0.4/plugin/src/CoqCoreInductives.ml#L54)
