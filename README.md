# potpie
Proof Object Transformation, Preserving Imp Embeddings: the first proof compiler to be formally proven correct

## Arxiv link
TODO

## Guide to Code Referenced in the Paper

See [GUIDE.md](guide.md)

## How to Build

First, ensure that you have [Coq installed](https://coq.inria.fr/opam-using.html) (we've tested Potpie with
Coq 8.14.0, compiled with OCaml 4.12.0, on Mac OS 10.15.7 (intel) and
13.1 (m1) as well as Ubuntu).

Run `coq_makefile -f _CoqProject -o CoqMakefile`, then once that's
done, run `make`. It is okay (and expected) if the build seems to
pause near the end for about a minute.

When you first run `make`, the last few lines that are output should
look something like:

```
     : hl_stk AssignSmallCompiled.T.precond AssignSmallCompiled.T.program
         AssignSmallCompiled.T.postcond AssignSmallCompiled.T.fenv
Finished transaction in <60-ish> secs (<60-ish>u,<1-ish>s) (successful)
     = "Eval4"
     : string
```

And it should be all done!
