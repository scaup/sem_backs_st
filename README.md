This is the artifact for the following submission:
Purity of ST: Full Abstraction by Semantically Typed Back-translation

# Verifying f.a. from STLCmu into STLCmuST

To verify f.a. from STLCmu into STLCmuST, one needs to go over the following:

- The [STLCmu](theories/STLCmu)-folder which contains the standard representation of a cbv simply-typed lambda calculus with iso-recursive types: 
  + [lang.v](theories/STLCmu/lang.v) contains the expression/value grammar (fig 1) and the operational semantics (§2.1), 
  + [types.v](theories/STLCmu/types.v) the types (fig 1), 
  + [typing.v](theories/STLCmu/typing.v) the typing rules (§2.1), and
  + [contexts.v](theories/STLCmu/contexts.v) defines contexts together with their typing rules.

- The [STLCmuST](theories/STLCmuST)-folder contains the extension of STLCmu with the ST-monad: 
  + [lang.v](theories/STLCmuST/lang.v) contains the expression/value grammar (fig 1) and the operational semantics (§2.1), 
  + [types.v](theories/STLCmuST/types.v) the types (fig 1), 
  + [typing.v](theories/STLCmuST/typing.v) the typing rules (§2.1), and
  + [contexts.v](theories/STLCmuST/contexts.v) defines contexts together with their typing rules.

- [embedding_STLCmu_STLCmuST.v](theories/end_to_end/embedding_STLCmu_STLCmuST.v) defines the canonical embedding from STLCmu into STLCmuST on expressions and contexts.

- [back_ctx_STLCmuST_STLCmu.v](theories/end_to_end/back_ctx_STLCmuST_STLCmu.v) defines the uniform backtranslation on contexts from STLCmu to STLCmuST and proves that this backtranslation behaves correctly.

- [pres_ctx_equiv.v](theories/end_to_end/pres_ctx_equiv.v) defines contextual equivalence of both STLCmu and STLCmuST and proves that this equivalence is preserved under this canonical embedding.

- [refl_ctx_equiv.v](theories/end_to_end/refl_ctx_equiv.v) proves that contextual equivalence is reflected under this canonical embedding.

# Overview Coq Development

Here we give an overview of the most important directories/files.

- [./STLCmu](theories/STLCmu): This folder contains the completely standard definition of STLCmu (see above)
- [./STLCmuVS](theories/STLCmuVS): This folder contains the definition of STLCmuVS; STLCmu where we have added the VirtualStep-construct in the grammar of expressions, see [STLCmuVS/lang.v](theories/STLCmuVS/lang.v).
  This file also contains the evaluation rules for VirtualStep. 
  There are no additional typing rules however ([STLCmuVS/typing.v](theories/STLCmuVS/typing.v)) and (on the well-typed terms) STLCmuVS completely coincides with STLCmu which is proven in [STLCmu/boring.v](theories/STLCmu/boring.v) (while this fact is easy to see, formally proving it entails a lot of boilerplate code).
  + [virt_steps](theories/STLCmuVS/virt_steps): Provides lemma that `VirtStep v` always terminates.
  + [lib](theories/STLCmuVS/lib): This subfolder contains the definition of a fixpoint operator in [fixarrow.v](theories/STLCmuVS/lib/fixarrow.v) and divergent term in [omega.v](theories/STLCmuVS/lib/omega.v), both of which implemented using recursive types.
  + [logrel](theories/STLCmuVS/logrel): This subfolder contains the LR that defines the intermediate semantic language. 
    It contains the following files:
    * [definitions.v](theories/STLCmuVS/logrel/definitions.v): defines the LR (fig 2, §2.2.2)
    * [adequacy.v](theories/STLCmuVS/logrel/adequacy.v): defines adequacy of our logical relation (Lemma 2.1)
    * [compat_lemmas.v](theories/STLCmuVS/logrel/compat_lemmas.v): proves the compatibility lemmas
    * [fundamental.v](theories/STLCmuVS/logrel/fundamental.v): proves the fundamental theorem (Theorem 2.2)
    * [generic/lift.v](theories/STLCmuVS/logrel/generic/lift.v): defines the lift operator (Eq 3)
- [./end_to_end](theories/end_to_end): This folder contains the main theorems and the definitions to state them:
  + [embedding_STLCmu_STLCmuST.v](theories/end_to_end/embedding_STLCmu_STLCmuST.v) defines the canonical embedding from STLCmu into STLCmuST on expressions and contexts. 
  + [back_ctx_sem_STLCmuVS_syn_STLCmu.v](theories/end_to_end/back_ctx_sem_STLCmuVS_syn_STLCmu.v) proves Theorem 3.4; semantically-typed contexts can successfully be emulated by syntactically-typed ones.
  + [back_ctx_STLCmuST_sem_STLCmuVS.v](theories/end_to_end/back_ctx_STLCmuST_sem_STLCmuVS.v) proves Theorem 3.5; contexts in STLCmuST can be successfully emulated by semantically-typed contexts.
  + [back_ctx_STLCmuST_STLCmu.v](theories/end_to_end/back_ctx_STLCmuST_STLCmu.v) proves Theorem 3.6; contexts in STLCmuST can be successfully emulated by syntactically-typed contexts in STLCmu
  + [pres_ctx_equiv.v](theories/end_to_end/pres_ctx_equiv.v) defines contextual equivalence in STLCmu and STLCmuST (Definition 3.1), and proves preservation of contextual equivalence (Theorem 3.3)
  + [refl_ctx_equiv.v](theories/end_to_end/refl_ctx_equiv.v) proves reflection of contextual equivalence (Theorem 3.2)
- [./thms](theories/thms): This folder contains the same theorems as in [./end_to_end](theories/end_to_end), but stated wrt STLCmuVS and STLCmuST only (not STLCmu).
  The files in the latter ([./end_to_end](theories/end_to_end)) simply refer to the files here while applying the lemmas from [STLCmu/boring.v](theories/STLCmu/boring.v) (stating that STLCmu and STLCmuVS coincide on the syntactically well-typed part).
  + [back_ctx_sem_syn.v](theories/thms/back_ctx_sem_syn.v): Theorem 3.4 wrt STLCmuVS
  + [back_ctx_st_sem.v](theories/thms/back_ctx_st_sem.v): Theorem 3.5 wrt STLCmuVS
  + [back_ctx_st_syn.v](theories/thms/back_ctx_st_syn.v): Theorem 3.6 wrt STLCmuVS
  + [pres_ctx_equiv.v](theories/thms/pres_ctx_equiv.v): Theorem 3.3 wrt STLCmuVS
  + [refl_ctx_equiv.v](theories/thms/refl_ctx_equiv.v): Theorem 3.2 wrt STLCmuVS
- [./embedding](theories/embedding): This directory defines the natural embedding from STLCmuVS to STLCmuST on expressions, types, and contexts.
  In [STLCmu/boring.v](boring.v) we additionally "prove" that this embedding, composed with the one from STLCmu into STLCmuVS gives us the one from STLCmu into STLCmuST (defined in [embedding_STLCmu_STLCmuST.v](theories/end_to_end/embedding_STLCmu_STLCmuST.v)). 
- [prelude](theories/prelude): This directory defines some generic functions and lemmas we couldn't find in stdpp or the Iris library.
- [backtranslations](theories/backtranslations): This directory defines all the different parts of the back-translation together with their accompanying LRs or lemmas about the LRs
  + [un_syn](theories/backtranslations/un_syn): This subdirectory defines the translation of untyped code into the universe and its accompanying LRs.
    * [universe](theories/backtranslations/un_syn/universe): Here, we define the universal type in [base.v](theories/backtranslations/un_syn/universe/base.v) (see §4.1.1), together with some of its important properties in [paths.v](theories/backtranslations/un_syn/universe/paths.v)
    * [expressions.v](theories/backtranslations/un_syn/expressions.v) and [contexts.v](theories/backtranslations/un_syn/contexts.v) define the translation into the universe of expressions (fig 5) and contexts respectively. [typed.v](theories/backtranslations/un_syn/typed.v) proves the well-typedness of these translations
    * [logrel](theories/backtranslations/un_syn/logrel): This folder contains the file [definitions.v](theories/backtranslations/un_syn/logrel/definitions.v) that defines the two logical relations in §4.2 and §4.3.
      + [syn_le_un](theories/backtranslations/un_syn/logrel/syn_le_un): This subfolder contains the [compatibility lemmas](theories/backtranslations/un_syn/logrel/syn_le_un/compat_lemmas.v) and the [fundamental theorem](theories/backtranslations/un_syn/logrel/syn_le_un/fundamental.v) (Theorem 4.2) for the relations in §4.2.
      + [un_le_syn](theories/backtranslations/un_syn/logrel/un_le_syn): This subfolder contains the [compatibility lemmas](theories/backtranslations/un_syn/logrel/un_le_syn/compat_lemmas.v) and the [fundamental theorem](theories/backtranslations/un_syn/logrel/un_le_syn/fundamental.v) (Theorem 4.3) for the relations in §4.3.
  + [sem_syn](theories/backtranslations/sem_syn): this directory defines the remaining machinery from §4.
    * [embed_project.v](theories/backtranslations/sem_syn/embed_project.v) defines embed and project functions (fig 6)
    * [gamma_lib.v](theories/backtranslations/sem_syn/gamma_lib.v) defines some machinery related to let `let`-binding in Eq 7 and Eq 14.
    * [back_ctx.v](theories/backtranslations/sem_syn/back_ctx.v) defines Eq 6 and Eq 7.
    * [syn_le_sem](theories/backtranslations/sem_syn/syn_le_sem) contains the remaining machinery for §4.2
      + [connective.v](theories/backtranslations/sem_syn/syn_le_sem/connective.v) proves Lemma 4.1.
      + [ctx_syn_le_un.v](theories/backtranslations/sem_syn/syn_le_sem/ctx_syn_le_un.v) relates the two contexts as depicted in fig 7
    * [sem_le_syn](theories/backtranslations/sem_syn/sem_le_syn) contains the remaining machinery for §4.3
      + [guard_assert.v](theories/backtranslations/sem_syn/sem_le_syn/guard_assert.v) defines the guards/asserts (fig 10)
      + [connective.v](theories/backtranslations/sem_syn/sem_le_syn/connective.v) proves lemma 4.5
      + [ga_ctx.v](theories/backtranslations/sem_syn/sem_le_syn/ga_ctx.v) defines Eq 13 en Eq 14.
      + [ga_ctx_le_ep_ctx.v](theories/backtranslations/sem_syn/sem_le_syn/ga_ctx_le_ep_ctx.v) relates the two contexts as depicted in fig 9
      + We have [no_op.v](theories/backtranslations/sem_syn/sem_le_syn/no_op.v) and [ghost_step_ga.v](theories/backtranslations/sem_syn/sem_le_syn/ghost_step_ga.v) as an alternative to Lemma 4.6 in the paper. The relatedness of contexts in fig 8 is accordingly split up in two parts: [ctx_le_gs_ctx.v](theories/backtranslations/sem_syn/sem_le_syn/ctx_le_gs_ctx.v) and [gs_ctx_le_ga_ctx.v](theories/backtranslations/sem_syn/sem_le_syn/gs_ctx_le_ga_ctx.v) using our ghost steps as an intermediate stepping stone.
  + [st_sem](theories/backtranslations/st_sem): this directory defines the remaining machinery from §5.
    * [heap_emul](theories/backtranslations/st_sem/heap_emul): contains [base.v](theories/backtranslations/st_sem/heap_emul/base.v) defining our encoding function for a list of values, and [spec.v](theories/backtranslations/st_sem/heap_emul/spec.v) which proves the specifications given in §5.1
    
    * [expressions.v](theories/backtranslations/st_sem/expressions.v) defines the semantic back-translation on expressions
    * [contexts.v](theories/backtranslations/st_sem/contexts.v) on contexts

    * [well_defined/logrel](theories/backtranslations/st_sem/well_defined/logrel) contains the (theories/backtranslations/st_sem/well_defined/logrel/definition.v)[definition of the extend LR] (see §5.2), [the matching lemma](theories/backtranslations/st_sem/well_defined/logrel/matches_sem.v) (first equation in §5.2), the compatibility lemmas in [compat_lemmas_easy.v](theories/backtranslations/st_sem/well_defined/logrel/compat_lemmas_easy.v) and [compat_lemmas.v](theories/backtranslations/st_sem/well_defined/logrel/compat_lemmas.v), and [the fundamental theorem](theories/backtranslations/st_sem/well_defined/logrel/fundamental.v).
    * [correctnesss/sem_le_st](theories/backtranslations/st_sem/correctness/sem_le_st/): this folder contains the machinery for 5.3
      + [adequacy.v](theories/backtranslations/st_sem/correctness/sem_le_st/logrel/adequacy.v)
      + [definition.v](theories/backtranslations/st_sem/correctness/sem_le_st/logrel/definition.v)
      + [lift.v](theories/backtranslations/st_sem/correctness/sem_le_st/logrel/lift.v)
      + [compat_lemmas.v](theories/backtranslations/st_sem/correctness/sem_le_st/logrel/compat_lemmas.v): compatibility lemmas wrt the ST primitives
      + [compat_lemmas_easy.v](theories/backtranslations/st_sem/correctness/sem_le_st/logrel/compat_lemmas_easy.v): other compatibility lemmas
      + [fundamental.v](theories/backtranslations/st_sem/correctness/sem_le_st/logrel/fundamental.v)
    * [correctnesss/st_le_sem](theories/backtranslations/st_sem/correctness/sem_le_st/): this folder contains the machinery for the other refinement (point (3) in the intro of §5)
      + [adequacy.v](theories/backtranslations/st_sem/correctness/st_le_sem/logrel/adequacy.v)
      + [definition.v](theories/backtranslations/st_sem/correctness/st_le_sem/logrel/definition.v)
      + [lift.v](theories/backtranslations/st_sem/correctness/st_le_sem/logrel/lift.v)
      + [compat_lemmas.v](theories/backtranslations/st_sem/correctness/st_le_sem/logrel/compat_lemmas.v): compatibility lemmas wrt to the ST primitives
      + [compat_lemmas_easy.v](theories/backtranslations/st_sem/correctness/st_le_sem/logrel/compat_lemmas_easy.v): other compatibility lemmas
      + [fundamental.v](theories/backtranslations/st_sem/correctness/st_le_sem/logrel/fundamental.v)

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

opam install coq.8.13.2 coq-iris.dev.2021-08-10.0.e252ca6e coq-autosubst
```

## Compiling proofs

Run make inside of this directory; get a coffee or something.

# Credits

definition STLang and some lemmas regarding its reduction are taken and adjusted from:
https://dl.acm.org/doi/10.1145/3158152
