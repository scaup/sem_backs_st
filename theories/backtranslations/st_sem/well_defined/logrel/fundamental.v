From iris Require Import program_logic.weakestpre.
From st.lamst Require Import lang types typing.
From st.lam Require Import lang wkpre generic.lift.
From st.backtranslations.st_sem Require Import ghost heap_emul.base expressions.
From st.backtranslations.st_sem.well_defined.logrel Require Import definition compat_lemmas.
From iris.proofmode Require Import tactics.

Section fundamental_theorem.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.
  Context `{ghost_mapG_inst : !ghost_mapG Σ nat (prod val val)}.

  Set Nested Proofs Allowed.

  Lemma fundamental (Γ : list lamst.types.type) (e : lamst.lang.expr) (τ : lamst.types.type)
        (d : Γ ⊢ₛₜ e : τ) :
    open_exprel_typed Γ <<e>> <<e>> τ.
  Proof.
    induction d; simpl.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - by apply compat_alloc.
    - by apply compat_read.
    - by eapply compat_write.
    - by eapply compat_bind.
    - by apply compat_retrn.
    - by apply compat_runst.
    - by eapply compat_equal.
  Admitted.

End fundamental_theorem.
