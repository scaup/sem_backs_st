From st.STLCmuST Require Import lang types typing.
From st.STLCmu Require Import types lang typing contexts.
From st.STLCmuST Require Import contexts.
From st.embedding Require Import types.
From st.thms Require Import back_ctx_st_sem.
From st.STLCmu Require Import boring.
From st.end_to_end Require Import embedding_STLCmu_STLCmuST.
From st.STLCmuVS Require Import lang.
From st Require Import resources.

Section back_ctx_STLCmuST_sem_STLCmuVS.

  (* Given any syntactically-typed context in STLCmuST, ⊢ₛₜ C : ([[Γ]];[[τ]]) ⇒ ([];1), *)
  Context (C : ctx)
          (Γ : list type) (pΓ : Forall Closed Γ) (τ : type) (pτ : Closed τ)
          (pC : typed_ctx C (embed <$> Γ) (embed τ) [] (embed TUnit)).

  (* we have a semantically-typed context in STLCmuVS, C_b, *)
  Definition back_ctx_STLCmuST_sem_STLCmuVS : STLCmuVS.contexts.ctx :=
    back_ctx_st_sem C.

  (* It is indeed semantically-typed of (Γ;τ) ⇒ ([];1) *)
  Lemma back_ctx_STLCmuST_sem_STLCmuVS_typed :
    ∀ {Σ} {semΣ_inst : semΣ Σ},
      logrel.definitions.ctx_rel_typed MaybeStuck
                                         back_ctx_STLCmuST_sem_STLCmuVS
                                         back_ctx_STLCmuST_sem_STLCmuVS
                                           Γ τ [] TUnit.
  Proof. by apply back_ctx_st_sem_sem_typed. Qed.

  (* Furthermore, the backtranslated contexts successfully emulates the original (when interacting with syntactically typed terms in STLCmu). *)
  (* That is, for all syntactically typed e, Γ ⊢ₙₒ e : τ, C_b[e]⇓ ⇔ C[[[e]]]⇓ *)

  Lemma back_ctx_STLCmuST_sem_STLCmuVS_correct_emulation :
    ∀ (e : STLCmu.lang.expr) (de : Γ ⊢ₙₒ e : τ),
      STLCmuVS_halts (STLCmuVS.contexts.fill_ctx back_ctx_STLCmuST_sem_STLCmuVS (boring.embd_expr e)) <-> STLCmuST_halts (fill_ctx C (embd_expr e)).
  Proof.
    intros e de.
    rewrite -(comp_embeddings e).
    eapply back_ctx_st_sem_correct_emulation; eauto.
    by apply boring.embd_expr_typed.
  Qed.

End back_ctx_STLCmuST_sem_STLCmuVS.
