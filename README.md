This is the artifact for the following submission:
Purity of ST: Full Abstraction by Semantically Typed Back-translation

# Results from paper linked with Coq code

| Main theorems from the paper                                                 | File in Coq project                  |
|------------------------------------------------------------------------------|--------------------------------------|
| Theorem 3.2 (reflection of contextual equivalence)                           | theories/thms/refl_equiv.v           |
| Theorem 3.3 (preservation of contextual equivalence with slight restriction) | theories/thms/pres_nr_lam_equiv.v    |
| Theorem 3.4 (Uniform backtranslation; STLCmuST -> Syntact. STLC)             | theories/thms/uni_back_ctx_st_syn.v  |
| Theorem 3.5 (Faithfully emulating stateful contexts by semantic contexts)    | theories/thms/uni_back_ctx_st_sem.v  |
| Theorem 3.6 (Faithfully emulating semantic contexts by pure contexts)        | theories/thms/uni_back_ctx_sem_syn.v |

# Compiling Proofs

## Installing right version of Coq and required libraries (Iris and Autsubst)

Get [opam](http://opam.ocaml.org/doc/Install.html)

The following commands create a new switch, activate it and install the right versions of Coq, Iris, and Autosubst.

```
opam switch create sembackst ocaml-base-compiler.4.12.0
eval $(opam env)

opam repo add coq-released https://coq.inria.fr/opam/released 
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update

opam install coq.8.13.2 coq-iris.dev.2021-03-23.1.66943a85 coq-iris-string-ident.dev coq-autosubst
```

## Compiling proofs

Run make inside of this directory; get a coffee or something.

# Credits

definition STLang and some lemmas regarding its reduction are taken and adjusted from:
https://dl.acm.org/doi/10.1145/3158152
