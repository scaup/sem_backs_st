From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.
From st.prelude Require Import big_op_three.

From st.lamst Require Import lang types typing.
From st.lam Require Import lang wkpre.

From st.backtranslations.st_sem Require Import expressions ghost heap_emul.base.
From st.backtranslations.st_sem.correctness.sem_le_st.logrel Require Import lift definition compat_lemmas.

Section fundamental_theorem.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Context `{genHeapG_inst : !gen_heapG loc lamst.lang.val Σ}.

  Context `{val_ghost_mapG_inst : !ghost_mapG Σ nat val}.
  Context `{loc_ghost_mapG_inst : !ghost_mapG Σ nat loc}.

  Lemma fundamental (Γ : list lamst.types.type) (e : lamst.lang.expr) (τ : lamst.types.type)
        (d : Γ ⊢ₛₜ e : τ) :
    open_exprel_typed Γ <<e>> e τ.
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
      (* !! intersting ones !! *)
    - by apply compat_alloc.
    - by apply compat_read.
    - apply (compat_write _ _ _ _ _ _ _ IHd1 IHd2). (* "by eapply"; why so long? *)
    - eapply compat_bind. exact IHd1. exact IHd2.
    - by apply compat_retrn.
    - by apply compat_runst.
    - by eapply compat_compare.
  Admitted.

End fundamental_theorem.
