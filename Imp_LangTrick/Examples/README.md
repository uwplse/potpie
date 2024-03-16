Case Studies
==========

Here we have the case studies presented in the paper, (in addition to
some more that we did not have room for.)

## Section (REF): Partial Correctness with Incorrect Compilation
The demonstrating partial correctness even in the face of incorrect
compilation can be found in the following files:

 - Helper function (multiplication and exponentiation): `SeriesHelperCompilation.v`
 - Series example: `SeriesExampleProofCompiled.v`
   and `SeriesExampleProofCompiledOther.v`
 - Square root example: `SquareRoot.v`
 
The corresponding compiler is instantiated in `/Imp_LangTrick/CodeCompiler/EnvToStackLTtoLEQ`.

## Additional Case Studies: PotPie 3 Ways

|                         | **Shift (Complete Spec)** | **Max (Partial Spec)** | **Min (Partial Spec)**  | **Proof Burden** |
|-------------------------|----------------------|-------------------|--------------------|----------------|
| **Incomplete**          | Y                    |                   |                    | Per-Proof      |
| **Incorrect**           |                      | Y                 |                    | Per-Proof      |
| **Unverified Correct**  | Y                    | Y                 | Y                  | Per-Proof      |


PotPie makes it easy to swap out control-flow-preserving program
compilers and still reuse the same infrastructure. We instantiate
\sysname with three different variants of a program compiler:

1. An **incomplete program compiler** that is missing entire cases of
   the source language grammar. So long as the programs being compiled
   do not use the unimplemented cases in the compiler, we can still
   prove the user proof obligations to acquire target-level
   guarantees.
2. An **incorrect program compiler** that contains a mistake and an
   unsafe optimization, in a similar vein to the previous examples.
3. Fixing the bugs gets an **unverified correct program compiler**
   that always preserves program and specification behavior, and thus
   makes the invocation user proof burdens always satisfiable.
   We can now \emph{always} satisfy the user proof obligations needed
   to invoke its associated proof compiler for any source program and
   proof.

The above table outlines these case studies for a simple set of programs we consider.
For those programs, we have two primary takeaways.

1.  First, PotPie can be used to get target-level proofs about certain
    programs even when the program compiler is still under
    development.
2.  Second, compilation of proofs about partial specifications in the
    face of incorrect compilation is sometimes possible and sometimes
    not. The difference is not simply whether the compilation bug
    manifests in the compiled program, but rather whether it manifests
    _in a way that is relevant to meaningful specification
    preservation_.

These examples can be found in the following files:

- Shift (Complete Spec, Incomplete Compiler):
  `ExampleLeftShift_Incomplete.v`
- Max (Partial Spec):
  - Incorrect Compiler: `MaxIncorrectProofCompilationExample.v`
  - Unverified Correct Compiler: `MaxUnprovenCorrectProofCompilationExample.v`
- Min (Partial Spec, Unverified Correct Compiler): `MinProofCompilationExample.v`
