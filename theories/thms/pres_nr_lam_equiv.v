From st.thms Require Import uni_back_ctx_st_sem uni_back_ctx_sem_syn.
From st.lam Require Import lang nr_types types typing contexts scopedness.
From st.lamst Require Import lang types typing contexts.
From st.embedding Require Import types expressions typed.
From st.thms Require Import uni_back_ctx_st_syn.

Definition nr_lam_equiv (Γ : list nr_type) e1 e2 (τ : nr_type) :=
  (fmap nr_type_type Γ) ⊢ₙₒ e1 : τ ∧ (fmap nr_type_type Γ) ⊢ₙₒ e2 : τ ∧
  ∀ C (dC : lam.contexts.typed_ctx C (fmap nr_type_type Γ) τ [] lam.types.TUnit),
    lam_halts (lam.contexts.fill_ctx C e1) <-> lam_halts (lam.contexts.fill_ctx C e2).

Definition lam_st_equiv (Γ : list lamst.types.type) e1 e2 (τ : lamst.types.type) :=
  Γ ⊢ₛₜ e1 : τ ∧ Γ ⊢ₛₜ e2 : τ ∧
  ∀ C (dC : lamst.contexts.typed_ctx C Γ τ [] lamst.types.TUnit),
    lamst_halts (lamst.contexts.fill_ctx C e1) <-> lamst_halts (lamst.contexts.fill_ctx C e2).

Theorem preservation_nr_lam_equiv Γ e1 e2 τ :
  nr_lam_equiv Γ e1 e2 τ → lam_st_equiv (fmap (embed ∘ nr_type_type) Γ) [[e1]] [[e2]] (embed (nr_type_type τ)).
Proof.
  intros (de1 & de2 & Hequiv); repeat split; try (by rewrite list_fmap_compose; apply embd_typed).
  - intro StHalts.
    eapply uni_back_ctx_correct; eauto.
    apply Hequiv; first by apply uni_back_ctx_typed.
    eapply uni_back_ctx_correct; eauto.
  - intro SynHalts.
    eapply uni_back_ctx_correct; eauto.
    apply Hequiv; first by apply uni_back_ctx_typed.
    eapply uni_back_ctx_correct; eauto.
Qed.
