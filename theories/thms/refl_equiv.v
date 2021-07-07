From st.lam Require Import lang nr_types types typing contexts scopedness.
From st.lamst Require Import lang types typing contexts.
From st.embedding Require Import types expressions typed contexts.
From st.thms Require Import pres_nr_lam_equiv.
From st.backtranslations.st_sem Require Import retraction.
From st.backtranslations.st_sem.correctness Require Import
     sem_le_st.logrel.definition sem_le_st.logrel.adequacy sem_le_st.logrel.fundamental
     st_le_sem.logrel.definition st_le_sem.logrel.adequacy st_le_sem.logrel.fundamental.


Definition lam_equiv (Γ : list lam.types.type) e1 e2 (τ : lam.types.type) :=
  Γ ⊢ₙₒ e1 : τ ∧ Γ ⊢ₙₒ e2 : τ ∧
  ∀ C (dC : lam.contexts.typed_ctx C Γ τ [] lam.types.TUnit),
    lam_halts (lam.contexts.fill_ctx C e1) <-> lam_halts (lam.contexts.fill_ctx C e2).

Theorem reflection_equiv Γ e1 e2 τ :
  Γ ⊢ₙₒ e1 : τ → Γ ⊢ₙₒ e2 : τ →
  lam_st_equiv (fmap embed Γ) (embd_expr e1) (embd_expr e2) (embed τ) →
  lam_equiv Γ e1 e2 τ.
Proof.
  intros de1 de2. intros (de1' & de2' & Hequiv). repeat split; auto.
  - intro LamHalts.
    specialize (Hequiv (embd_ctx C) (embd_ctx_typed C _ _ _ _ dC)).
    cut (lamst_halts (fill_ctx (embd_ctx C) [[e2]])).
    { apply st_le_sem.logrel.adequacy.exprel_adequate.
      intros Σ st_le_semΣ.
      cut (@open_exprel_typed Σ st_le_semΣ [] (fill_ctx (embd_ctx C) [[e2]]) (lam.contexts.fill_ctx C e2) TUnit).
      { intro H. specialize (H [] [] []). asimpl in H. apply H. }
      rewrite comm_fill_ctx_embd.
      rewrite <- (retraction (lam.contexts.fill_ctx C e2)) at 2.
      apply st_le_sem.logrel.fundamental.fundamental.
      change [] with (fmap embed []). change TUnit with (embed lam.types.TUnit).
      apply embd_typed. eapply lam.contexts.typed_ctx_typed; eauto.
    }
    apply Hequiv.
    { eapply sem_le_st.logrel.adequacy.exprel_adequate; eauto.
      intros Σ sem_le_stΣ.
      cut (@sem_le_st.logrel.definition.open_exprel_typed Σ sem_le_stΣ [] (lam.contexts.fill_ctx C e1) (fill_ctx (embd_ctx C) [[e1]]) TUnit).
      { intro H. specialize (H [] [] []). asimpl in H. apply H. }
      rewrite comm_fill_ctx_embd.
      rewrite <- (retraction (lam.contexts.fill_ctx C e1)) at 1.
      apply sem_le_st.logrel.fundamental.fundamental.
      change [] with (fmap embed []). change TUnit with (embed lam.types.TUnit).
      apply embd_typed. eapply lam.contexts.typed_ctx_typed; eauto.
    }
  - intro LamSTHalts.
    specialize (Hequiv (embd_ctx C) (embd_ctx_typed C _ _ _ _ dC)).
    cut (lamst_halts (fill_ctx (embd_ctx C) [[e1]])).
    { apply st_le_sem.logrel.adequacy.exprel_adequate.
      intros Σ st_le_semΣ.
      cut (@open_exprel_typed Σ st_le_semΣ [] (fill_ctx (embd_ctx C) [[e1]]) (lam.contexts.fill_ctx C e1) TUnit).
      { intro H. specialize (H [] [] []). asimpl in H. apply H. }
      rewrite comm_fill_ctx_embd.
      rewrite <- (retraction (lam.contexts.fill_ctx C e1)) at 2.
      apply st_le_sem.logrel.fundamental.fundamental.
      change [] with (fmap embed []). change TUnit with (embed lam.types.TUnit).
      apply embd_typed. eapply lam.contexts.typed_ctx_typed; eauto.
    }
    apply Hequiv.
    { eapply sem_le_st.logrel.adequacy.exprel_adequate; eauto.
      intros Σ sem_le_stΣ.
      cut (@sem_le_st.logrel.definition.open_exprel_typed Σ sem_le_stΣ [] (lam.contexts.fill_ctx C e2) (fill_ctx (embd_ctx C) [[e2]]) TUnit).
      { intro H. specialize (H [] [] []). asimpl in H. apply H. }
      rewrite comm_fill_ctx_embd.
      rewrite <- (retraction (lam.contexts.fill_ctx C e2)) at 1.
      apply sem_le_st.logrel.fundamental.fundamental.
      change [] with (fmap embed []). change TUnit with (embed lam.types.TUnit).
      apply embd_typed. eapply lam.contexts.typed_ctx_typed; eauto.
    }
Qed.
