From st.thms Require Import back_ctx_st_sem back_ctx_sem_syn.
From st.embedding Require Import types expressions typed.
From st.lamst Require Import lang types typing.
From st.lam Require Import lang types typing contexts scopedness.
From st.lamst Require Import contexts.
From st.backtranslations.st_sem Require Import scoped.

Section back_ctx_st_syn.

  (* Given any syntactically-typed context in lamst, ⊢ₛₜ C : ([[Γ]];[[τ]]) ⇒ ([];1), *)
  Context (C : ctx)
          (Γ : list type) (pΓ : Forall Closed Γ) (τ : type) (pτ : Closed τ)
          (pC : typed_ctx C (embed <$> Γ) (embed τ) [] (embed TUnit)).

  (* we have a syntactically typed context, C_b, *)
  Definition back_ctx_st_syn : lam.contexts.ctx :=
    (back_ctx_sem_syn (back_ctx_st_sem C) Γ τ).

  (* It is indeed syntactically typed of (Γ;τ) ⇒ ([];1) *)
  Lemma back_ctx_st_syn_syn_typed :
    |C> [] ⊢ₙₒ back_ctx_st_syn ☾ Γ ; τ ☽ : TUnit.
  Proof.
    apply back_ctx_sem_syn_typed; auto.
    change 0 with (length ([] : list lamst.types.type)).
    replace (length Γ) with (length (embed <$> Γ)) by by rewrite fmap_length.
    eapply back_ctx_scope; eauto.
  Qed.

  (* Furthermore, the backtranslated contexts successfully emulates the original (when interacting with syntactically typed terms in lam). *)
  (* That is, for all syntactically typed e, Γ ⊢ₙₒ e : τ, C_b[e]⇓ ⇔ C[[[e]]]⇓ *)

  Lemma back_ctx_st_syn_correct_emulation :
    ∀ (e : expr) (de : Γ ⊢ₙₒ e : τ),
      lam_halts (lam.contexts.fill_ctx back_ctx_st_syn e) <-> lamst_halts (fill_ctx C (embd_expr e)).
  Proof.
    assert (H1 : |sC> 0 ⊢ₙₒ back_ctx_st_sem C ☾ length Γ ☽).
    { change 0 with (length ([] : list lamst.types.type)).
      replace (length Γ) with (length (embed <$> Γ)) by by rewrite fmap_length.
      eapply back_ctx_scope; eauto. }
    pose proof (back_ctx_st_sem_sem_typed C Γ τ).
    intros e de.
    split; intros.
      eapply back_ctx_st_sem_correct_emulation, back_ctx_sem_syn_correct_emulation; eauto.
      eapply back_ctx_sem_syn_correct_emulation, back_ctx_st_sem_correct_emulation; eauto.
  Qed.

End back_ctx_st_syn.
