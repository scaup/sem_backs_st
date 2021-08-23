From st.thms Require Import back_ctx_st_syn.
From st.STLCmu Require Import types lang typing contexts.
From st.STLCmuST Require Import lang types typing contexts.
From st.embedding Require Import types typed.
From st.STLCmu Require Import boring.
From st.end_to_end Require Import embedding_STLCmu_STLCmuST back_ctx_STLCmuST_STLCmu.

Definition STLCmu_equiv Γ e1 e2 τ :=
  Forall Closed Γ ∧ Closed τ ∧
  Γ ⊢ₙₒ e1 : τ ∧ Γ ⊢ₙₒ e2 : τ ∧
  ∀ C (dC : STLCmu.contexts.typed_ctx C Γ τ [] STLCmu.types.TUnit),
    STLCmu_halts (STLCmu.contexts.fill_ctx C e1) <-> STLCmu_halts (STLCmu.contexts.fill_ctx C e2).

Definition STLCmuST_equiv (Γ : list type) e1 e2 (τ : type) :=
  Forall Closed Γ ∧ Closed τ ∧
  Γ ⊢ₛₜ e1 : τ ∧ Γ ⊢ₛₜ e2 : τ ∧
  ∀ C (dC : STLCmuST.contexts.typed_ctx C Γ τ [] STLCmuST.types.TUnit),
    STLCmuST_halts (STLCmuST.contexts.fill_ctx C e1) <-> STLCmuST_halts (STLCmuST.contexts.fill_ctx C e2).

Theorem preservation_STLCmu_equiv Γ e1 e2 τ :
  STLCmu_equiv Γ e1 e2 τ → STLCmuST_equiv (embed <$> Γ) [[e1]] [[e2]] (embed τ).
Proof.
  intros (dΓ & dτ & de1 & de2 & Hequiv).
  repeat split.
  (* bookkeeping *)
  eapply Forall_fmap, Forall_impl; eauto. intros. by apply embed_pres_closed.
  by apply embed_pres_closed.
  by rewrite -comp_embeddings; apply embd_typed, boring.embd_expr_typed.
  by rewrite -comp_embeddings; apply embd_typed, boring.embd_expr_typed.
  (* okay *)
  - intro Halts.
    eapply back_ctx_STLCmuST_STLCmu_correct_emulation; eauto.
    apply Hequiv; first by apply back_ctx_STLCmuST_STLCmu_typed.
    eapply back_ctx_STLCmuST_STLCmu_correct_emulation; eauto.
  - intro SynHalts.
    eapply back_ctx_STLCmuST_STLCmu_correct_emulation; eauto.
    apply Hequiv; first by apply back_ctx_STLCmuST_STLCmu_typed.
    eapply back_ctx_STLCmuST_STLCmu_correct_emulation; eauto.
Qed.
