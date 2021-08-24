This is the artifact for the following submission:
Purity of ST: Full Abstraction by Semantically Typed Back-translation

# Verifying main result only:

To verify the main result, one needs to go over the following:

- The [STLCmu](theories/STLCmu)-folder which contains the standard representation of a cbv simply-typed lambda calculus with equirecursive types: [lang.v](theories/STLCmu/lang.v) contains the grammar and the operational semantics, [types.v](theories/STLCmu/types.v) the types, and [typing.v](theories/STLCmu/typing.v) the typing rules.
  [contexts.v](theories/STLCmu/contexts.v) defines contexts together with their typing rules.

- The [STLCmuST](theories/STLCmuST)-folder contains the extension of STLCmu with the ST-monad: [lang.v](theories/STLCmuST/lang.v) contains the grammar and the operational semantics, [types.v](theories/STLCmuST/types.v) the types, and [typing.v](theories/STLCmuST/typing.v) the typing rules.
  [contexts.v](theories/STLCmuST/contexts.v) defines contexts together with their typing rules.

- [embedding_STLCmu_STLCmuST.v](theories/end_to_end/embedding_STLCmu_STLCmuST.v) defines the canonical embedding from STLCmu into STLCmuST.

- [back_ctx_STLCmuST_STLCmu.v](theories/end_to_end/back_ctx_STLCmuST_STLCmu.v) defines the uniform backtranslation on contexts from STLCmu to STLCmuST and proves that this backtranslation behaves correctly.

- [pres_ctx_equiv.v](theories/end_to_end/pres_ctx_equiv.v) defines contextual equivalence of both STLCmu and STLCmuST and proves that this equivalence is preserved under this canonical embedding.

- [refl_ctx_equiv.v](theories/end_to_end/refl_ctx_equiv.v) proves that contextual equivalence is reflected under this canonical embedding.

# Results from paper linked with Coq code (todo: update)

| Main theorems from the paper                                                 | File in Coq project                  |
|------------------------------------------------------------------------------|--------------------------------------|
| Theorem 3.2 (reflection of contextual equivalence)                           | theories/thms/refl_equiv.v           |
| Theorem 3.3 (preservation of contextual equivalence with slight restriction) | theories/thms/pres_nr_STLCmuVS_equiv.v    |
| Theorem 3.4 (Uniform backtranslation; STLCmuST -> Syntact. STLC)             | theories/thms/uni_back_ctx_st_syn.v  |
| Theorem 3.5 (Faithfully emulating stateful contexts by semantic contexts)    | theories/thms/uni_back_ctx_st_sem.v  |
| Theorem 3.6 (Faithfully emulating semantic contexts by pure contexts)        | theories/thms/uni_back_ctx_sem_syn.v |

# Directory Structure (todo: update)

- STLCmuVS : contains the definition of the pure language
  + logrel : LR for the definition of semantically typed intermediate language
- STLCmuST : contains the definition of the extended language with the ST monad
- embedding : the embedding from the pure language into the one with ST
- backtranslations
  + st_sem : the backtranslation from ST contexts into semantic contexts (and with it, the necessary LR's)
  + un_syn : the backtranslation from untyped terms into our universe (and with it, the necessary LR's)
  + sem_syn : the wrappers (guard/assert) and (embed/project) on non-recusrive types; the lemmas connecting our typed and untyped LR's; the lemmas that (guard/assert) are can be freely added to the right of our LR for the intermediate language
- thms : proofs of the main theorems as in the table above

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
