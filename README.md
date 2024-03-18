# potpie
Potpie is a framework for specification-preserving proof compilation
even when the program compiler technically miscompiles the program. As
long as the miscompilation does not violate a program's (possibly
partial) specification, we can compile the program, specification, and
proof that the program meets the specification all at once.

If you're reading this in the included zip file, you can also find our
code base [on GitHub](https://github.com/uwplse/potpie/tree/v0.4).

<!-- ## Arxiv link -->
<!-- TODO -->

## Guide to Code Referenced in the Paper

See [GUIDE.md](GUIDE.md) for a list of all the pointers to places in the code we
referenced in the paper, with links to the associated files.


## Workflows
Potpie has two main workflows for proof compilation. Both require
program and specification compilers that preserve the structure of
proofs. The first one, Tree, is based around a proof compiler that
separates computation from the proof of correctness. The other
workflow, CC, is <b>c</b>orrect by <b>c</b>onstruction, and thus does
not separate computation and proof. Both workflows are parametric in
the choice of program and specification compilers.

### Tree: Proof Tree Compilation
A Tree proof compiler operates on the proof tree structure, treating
it as a data structure instead of as a proof. Given a source level
Hoare proof, it produces a target level Hoare proof _tree_.

This tree can then be checked using our Coq plugin, written in
OCaml. The plugin contains a certificate generator and a yes/no
checking algorithm. The plugin, when invoked, can return one of
several answers:

1. A certificate, which takes the type `StkHoareTree.stk_valid_tree`. If this
   certificate typechecks in Coq, then the compiled tree is
   valid.
2. The Coq bool value `true`: the target tree is valid according to
   our tree-checking algorithm, but the certificate generator was
   unable construct the certificate. This can happen in a couple of
   situations that we outline below.
3. The Coq bool value `false`: the target tree is most decidedly _not_
   valid, according to our tree-checking algorithm.
   
In order to construct a certificate, the plugin has to find all of the
necessary evidence in order to apply one of the constructors for
`StkHoareTree.stk_valid_tree`. This involves constructing proof terms
using either reflection or by applying lemmas we have defined in Coq
to various terms. This is done in OCaml code so that we can leverage
syntactic equality over Coq Props, which is decidable. Equality of
Props is not decidable in Coq.

The plugin may fail to create a certificate for an otherwise valid
proof tree if the program in question utilizes mutually recursive
functions. In that case, we instead run the boolean checking
algorithm, which is theoretically able to handle these cases.

If the plugin does create a certificate that typechecks, the user
should check it to ensure that it is still proving the validity of the
same Hoare triple as the desired target level triple. For a Hoare
triple `{P} c {Q}`, the plugin should never recurse into `P` or `Q`
and certainly should not modify them.


### CC: Correct-by-Construction Proof Compilation
A CC proof compiler instead operates on the source Hoare logic proof,
and produces a target Hoare logic proof. This is not just the data
structure, as in Tree -- it will also contain its proof of
correctness. In order to instantiate a CC proof compiler using a given
program and specification compiler, a user first has to show that the
program and specification compilers satisfy a particular set of
equations. After this, the user will have to additionally prove a set
of user proof obligations, that have to be shown for each proof they
wish to compile. This creates a lot more up-front work than the Tree
workflow, but it is sound in that whenever program's specification is
preserved by compilation, then the proof should be compilable using
this method.

## Organization
Our code is organized into two main folders, `Imp_LangTrick` and
`plugin`. The `Imp_LangTrick` directory contains the majority of our
proof development, and the entirety of the CC proof compilation
workflow. The Tree workflow spans both directories, with the Coq
plugin contained in the `plugin` directory.

## How to Build

### Installing Coq

First, ensure that you have [Coq installed](https://coq.inria.fr/opam-using.html) (we've tested Potpie with
Coq 8.16.1, compiled with OCaml 4.12.0, on Mac OS 10.15.7 (intel) and
13.1 (m1) as well as Ubuntu).

#### Using Opam on Unix
The following should take care of almost everything.
```
opam switch create potpie-switch 4.12.0
opam pin add coq 8.16.1
opam install dune
```

Optionally, you can also install CoqIDE:

```
opam install coqide
```

Be sure to follow all additional instructions that `opam` may direct
you to take, such as running `eval $(opam env)` as necessary.


### Actually Building
In order to build our proof development and the plugin together, we
use the `dune` build system. In the main directory of this repo, run

```
dune build
```

It takes a few minutes to build, especially the first time. This will
both compile the OCaml code and also run `coqc` on all of our Coq
files.

#### Use with _CoqProject
Since many Coq editors still require a `_CoqProject` file in order to
find compiled, we include `_CoqProject` files in both the
`Imp_LangTrick` and `plugin` directories.

Running `make` in the `Imp_LangTrick` directory should still
work. However, we do not use `make` for the plugin and only really use
dune.
