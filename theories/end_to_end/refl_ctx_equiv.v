From st.STLCmu Require Import lang typing types contexts.
From st.STLCmuST Require Import lang types typing contexts.
From st.embedding Require Import types.
From st.end_to_end Require Import embedding_STLCmu_STLCmuST pres_ctx_equiv refl_ctx_equiv_help.

Theorem reflection_equiv (Γ : list STLCmu.types.type) e1 e2 (τ : STLCmu.types.type) :
  STLCmuST_equiv (fmap embed Γ) (embd_expr e1) (embd_expr e2) (embed τ) →
  STLCmu_equiv Γ e1 e2 τ.
Proof.
  (* admin *)
  intros (pΓ & pτ & de1 & de2 & H).
  assert (de1' : Γ ⊢ₙₒ e1 : τ). by apply embd_expr_typed_inv.
  assert (de2' : Γ ⊢ₙₒ e2 : τ). by apply embd_expr_typed_inv.
  do 4 try split; auto.
  pose proof (iffLR (Forall_fmap _ _ _) pΓ). eapply Forall_impl; eauto.
  simpl. intros. by apply embed_Closed_n_inv. by apply embed_Closed_n_inv.
  (* okay *)
  intros C dC.
  assert (dC' : typed_ctx (embd_ctx C) (embed <$> Γ) [|τ|] [] TUnit).
  { change [] with (embed <$> []).
    change TUnit with (embed STLCmu.types.TUnit).
    rewrite -boring.comp_embeddings_ctx.
    by apply contexts.embd_ctx_typed, boring.embd_ctx_typed.
  }
  specialize (H (embd_ctx C) dC').
  split; intro halts.
  - apply embd_expr_halts_iff; first by eapply STLCmu.contexts.typed_ctx_typed; eauto.
    rewrite -comm_fill_ctx_embd.
    apply H.
    rewrite comm_fill_ctx_embd.
    by apply embd_expr_halts_iff; first by eapply STLCmu.contexts.typed_ctx_typed; eauto.
  - apply embd_expr_halts_iff; first by eapply STLCmu.contexts.typed_ctx_typed; eauto.
    rewrite -comm_fill_ctx_embd.
    apply H.
    rewrite comm_fill_ctx_embd.
    by apply embd_expr_halts_iff; first by eapply STLCmu.contexts.typed_ctx_typed; eauto.
Qed.
