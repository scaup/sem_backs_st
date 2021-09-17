From st.STLCmu Require Import types lang typing.
From st.embedding Require Import types.
From st.thms Require Import back_ctx_sem_syn.
From st.STLCmu Require Import boring.
From st.end_to_end Require Import embedding_STLCmu_STLCmuST.
From st.STLCmuVS Require Import lang contexts scopedness logrel.definitions.
From st.STLCmu Require Import contexts.
From st Require Import resources.

Section back_ctx_sem_STLCmuVS_syn_STLCmu.

  (* Given any semantically-typed context in STLCmuVS, ⊨ C : (Γ;τ) ⇒ ([];1), *)
  Context (C : STLCmuVS.contexts.ctx)
          (Γ : list type) (pΓ : Forall Closed Γ) (τ : type) (pτ : Closed τ)
          (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽) (* Formally, our LR does not enforce well-scopedness, so we add the constraint here explicitly *)
          (pC : ∀ {Σ} {semΣ_inst : semΣ Σ}, ctx_rel_typed MaybeStuck C C Γ τ [] TUnit).

  (* we have a syntactically-typed context in STLCmu, C_b, *)
  Definition back_ctx_sem_STLCmuVS_syn_STLCmu : STLCmu.contexts.ctx :=
    boring.proj_ctx (back_ctx_sem_syn C Γ τ).

  (* It is indeed syntactically-typed of (Γ;τ) ⇒ ([];1) *)
  Lemma back_ctx_sem_STLCmuVS_syn_STLCmu_typed :
    typed_ctx back_ctx_sem_STLCmuVS_syn_STLCmu  Γ τ [] TUnit.
  Proof. by apply boring.proj_ctx_typed, back_ctx_sem_syn_typed. Qed.

  (* Furthermore, the backtranslated contexts successfully emulates the original (when interacting with syntactically typed terms in STLCmu). *)
  (* That is, for all syntactically typed e, Γ ⊢ₙₒ e : τ, C_b[e]⇓ ⇔ C[[[e]]]⇓ *)

  Lemma back_ctx_sem_STLCmuVS_syn_STLCmu_correct_emulation :
    ∀ (e : STLCmu.lang.expr) (de : Γ ⊢ₙₒ e : τ),
      STLCmu_halts (STLCmu.contexts.fill_ctx back_ctx_sem_STLCmuVS_syn_STLCmu e) <-> STLCmuVS_halts (STLCmuVS.contexts.fill_ctx C (boring.embd_expr e)).
  Proof.
    intros e de.
    apply (@iff_trans _ (STLCmuVS_halts (STLCmuVS.contexts.fill_ctx (boring.embd_ctx back_ctx_sem_STLCmuVS_syn_STLCmu) (boring.embd_expr e))) _).
    rewrite comm_embd_fill_ctx. eapply embd_expr_halts_iff.
    eapply typed_ctx_typed; eauto. apply back_ctx_sem_STLCmuVS_syn_STLCmu_typed.
    rewrite /back_ctx_sem_STLCmuVS_syn_STLCmu. erewrite inverse_ctx; try by eapply back_ctx_sem_syn_typed.
    apply back_ctx_sem_syn_correct_emulation; eauto.
    by apply boring.embd_expr_typed.
  Qed.

End back_ctx_sem_STLCmuVS_syn_STLCmu.
