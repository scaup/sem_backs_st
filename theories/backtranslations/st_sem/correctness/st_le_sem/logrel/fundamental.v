From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.

Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

From st.prelude Require Import big_op_three.

From st.lam Require Import lang.
From st.lamst Require Import wkpre lang types typing.

From st.backtranslations.st_sem Require Import expressions ghost heap_emul.base.
From st.backtranslations.st_sem.correctness.st_le_sem.logrel Require Import lift definition compat_lemmas.

Section fundamental_theorem.

  Context `{Σ : !gFunctors}.

  Context `{invG_inst : !invG Σ}.
  Context `{genHeapG_inst : !gen_heapG loc val Σ}.

  Context `{val_ghost_mapG_inst : !ghost_mapG Σ nat lam.lang.val}.
  Context `{loc_ghost_mapG_inst : !ghost_mapG Σ nat loc}.

  Opaque encode alloc read write bind retrn.

  Lemma fundamental (Γ : list lamst.types.type) (e : lamst.lang.expr) (τ : lamst.types.type)
        (d : Γ ⊢ₛₜ e : τ) :
    open_exprel_typed Γ e <<e>> τ.
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
    - by eapply compat_write.
    - by eapply compat_bind.
    - by apply compat_retrn.
    - by apply compat_runst.
    - by eapply compat_compare.
  Admitted.

End fundamental_theorem.
