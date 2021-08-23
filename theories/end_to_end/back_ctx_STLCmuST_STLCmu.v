From st.STLCmuST Require Import lang types typing.
From st.STLCmu Require Import types lang typing contexts.
From st.STLCmuST Require Import contexts.
From st.embedding Require Import types.
From st.thms Require Import back_ctx_st_syn.
From st.STLCmu Require Import boring.
From st.end_to_end Require Import embedding_STLCmu_STLCmuST.
From st.STLCmuVS Require Import lang.

Section back_ctx_STLCmuST_STLCmu.

  (* Given any syntactically-typed context in STLCmuST, ⊢ₛₜ C : ([[Γ]];[[τ]]) ⇒ ([];1), *)
  Context (C : ctx)
          (Γ : list type) (pΓ : Forall Closed Γ) (τ : type) (pτ : Closed τ)
          (pC : typed_ctx C (embed <$> Γ) (embed τ) [] (embed TUnit)).

  (* we have a syntactically typed context in STLCmu, C_b, *)
  Definition back_ctx_STLCmuST_STLCmu : STLCmu.contexts.ctx :=
    proj_ctx (back_ctx_st_syn C Γ τ).

  (* It is indeed syntactically typed of (Γ;τ) ⇒ ([];1) *)
  Lemma back_ctx_STLCmuST_STLCmu_typed :
    STLCmu.contexts.typed_ctx back_ctx_STLCmuST_STLCmu Γ τ [] TUnit.
  Proof. by apply proj_ctx_typed, back_ctx_st_syn_syn_typed. Qed.

  (* Furthermore, the backtranslated contexts successfully emulates the original (when interacting with syntactically typed terms in STLCmu). *)
  (* That is, for all syntactically typed e, Γ ⊢ₙₒ e : τ, C_b[e]⇓ ⇔ C[[[e]]]⇓ *)

  Lemma back_ctx_STLCmuST_STLCmu_correct_emulation :
    ∀ (e : STLCmu.lang.expr) (de : Γ ⊢ₙₒ e : τ),
      STLCmu_halts (STLCmu.contexts.fill_ctx back_ctx_STLCmuST_STLCmu e) <-> STLCmuST_halts (fill_ctx C (embd_expr e)).
  Proof.
    intros e de.
    rewrite -(comp_embeddings e).
    rewrite /back_ctx_STLCmuST_STLCmu.
    rewrite -(retraction e).
    erewrite comm_proj_fill_ctx; [ |apply back_ctx_st_syn_syn_typed; eauto].
    apply (@iff_trans _ (STLCmuVS_halts (contexts.fill_ctx (back_ctx_st_syn C Γ τ) (boring.embd_expr e))) _).
    - apply iff_sym. apply (proj_expr_halts_iff (contexts.fill_ctx (back_ctx_st_syn C Γ τ) (boring.embd_expr e)) [] TUnit).
      eapply contexts.typed_ctx_typed; [by apply boring.embd_expr_typed| apply back_ctx_st_syn_syn_typed; auto].
    - rewrite (retraction e). apply back_ctx_st_syn_correct_emulation; auto.
      by apply boring.embd_expr_typed.
  Qed.

End back_ctx_STLCmuST_STLCmu.
