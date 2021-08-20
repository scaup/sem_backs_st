From st.thms Require Import back_ctx_st_syn.
From st.STLCmuVS Require Import lang types types typing contexts scopedness.
From st.STLCmuST Require Import lang types types typing contexts.
From st.embedding Require Import types expressions typed.

Definition STLCmuVS_equiv Γ e1 e2 τ :=
  Forall Closed Γ ∧ Closed τ ∧
  Γ ⊢ₙₒ e1 : τ ∧ Γ ⊢ₙₒ e2 : τ ∧
  ∀ C (dC : STLCmuVS.contexts.typed_ctx C Γ τ [] STLCmuVS.types.TUnit),
    STLCmuVS_halts (STLCmuVS.contexts.fill_ctx C e1) <-> STLCmuVS_halts (STLCmuVS.contexts.fill_ctx C e2).

Definition STLCmuVS_st_equiv (Γ : list type) e1 e2 (τ : type) :=
  Forall Closed Γ ∧ Closed τ ∧
  Γ ⊢ₛₜ e1 : τ ∧ Γ ⊢ₛₜ e2 : τ ∧
  ∀ C (dC : STLCmuST.contexts.typed_ctx C Γ τ [] STLCmuST.types.TUnit),
    STLCmuST_halts (STLCmuST.contexts.fill_ctx C e1) <-> STLCmuST_halts (STLCmuST.contexts.fill_ctx C e2).

Theorem preservation_STLCmuVS_equiv Γ e1 e2 τ :
  STLCmuVS_equiv Γ e1 e2 τ → STLCmuVS_st_equiv (embed <$> Γ) [[e1]] [[e2]] (embed τ).
Proof.
  intros (dΓ & dτ & de1 & de2 & Hequiv).
  repeat split.
  (* bookkeeping *)
  eapply Forall_fmap, Forall_impl; eauto. intros. by apply embed_pres_closed.
  by apply embed_pres_closed. by apply embd_typed. by apply embd_typed.
  (* okay *)
  - intro Halts.
    eapply back_ctx_st_syn_correct_emulation; eauto.
    apply Hequiv; first by apply back_ctx_st_syn_syn_typed.
    eapply back_ctx_st_syn_correct_emulation; eauto.
  - intro SynHalts.
    eapply back_ctx_st_syn_correct_emulation; eauto.
    apply Hequiv; first by apply back_ctx_st_syn_syn_typed.
    eapply back_ctx_st_syn_correct_emulation; eauto.
Qed.
