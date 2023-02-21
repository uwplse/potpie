# potpie
Proof Object Transformation, Preserving Imp Embeddings: the first proof compiler to be formally proven correct

<!-- ## Arxiv link -->
<!-- TODO -->

## Guide to Code Referenced in the Paper

See [GUIDE.md](GUIDE.md)

## How to Build

### Installing Coq

First, ensure that you have [Coq installed](https://coq.inria.fr/opam-using.html) (we've tested Potpie with
Coq 8.14.0, compiled with OCaml 4.12.0, on Mac OS 10.15.7 (intel) and
13.1 (m1) as well as Ubuntu).

#### Using Opam

If you already have opam installed, and don't already have coq, use

```
opam pin add coq 8.14.0
```

Otherwise, if you don't want to mess with your current coq
installation, you can create a switch for PotPie:

```
opam switch create potpie-switch 4.12.0
opam pin add coq 8.14.0
```

Optionally, you can also install CoqIDE:

```
opam install coqide
```

Be sure to follow all additional instructions that `opam` may direct
you to take.

#### Via Coq Platform
Coq Platform installers for macOS and Windows are available
[here](https://github.com/coq/platform/releases/tag/2022.01.0). For
Linux, you can install using
[snap](https://snapcraft.io/coq-prover). Be sure to use version
`2022.01/stable`, or install via the command line with

```
sudo snap install coq-prover --channel=2022.01/stable
```

### Actually Building

Run `coq_makefile -f _CoqProject -o CoqMakefile`, then once that's
done, run `make`. It is okay (and expected) if the build seems to
pause near the end for about a minute. Then you can run `make`.

When you first run `make`, the last few lines that are output should
look something like:

```
     : hl_stk AssignSmallCompiled.T.precond AssignSmallCompiled.T.program
         AssignSmallCompiled.T.postcond AssignSmallCompiled.T.fenv
Finished transaction in <60-ish> secs (<60-ish>u,<1-ish>s) (successful)
     = "Eval4"
     : string
```

And that's it!
