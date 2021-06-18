From st.thms Require Import uni_back_ctx_st_sem uni_back_ctx_sem_syn.
From st.lam Require Import lang nr_types types typing contexts scopedness.
From st.lamst Require Import lang types typing contexts.
From st.embedding Require Import types expressions typed.

Section uni_back_ctx_st_syn.

  Context (Γ : list nr_type) (τ : nr_type).
  Context (C : lamst.contexts.ctx)
          (pC : lamst.contexts.typed_ctx C
                  (fmap (embed ∘ nr_type_type) Γ) (embed (nr_type_type τ)) [] (embed lam.types.TUnit)
          ).

  Definition uni_back_ctx : lam.contexts.ctx :=
    let Csem := uni_back_ctx_st_sem.uni_back_ctx C in
    uni_back_ctx_sem_syn.uni_back_ctx Csem Γ τ.

  Lemma uni_back_ctx_typed : lam.contexts.typed_ctx uni_back_ctx (fmap nr_type_type Γ) τ [] lam.types.TUnit.
  Proof.
    rewrite /uni_back_ctx.
    apply uni_back_ctx_sem_syn.uni_back_ctx_typed.
    pose proof (uni_back_ctx_scoped C (fmap nr_type_type Γ)).
    rewrite -list_fmap_compose in H. specialize (H τ pC). by rewrite fmap_length in H.
  Qed.

  Lemma uni_back_ctx_correct (e : lam.lang.expr) (de : lam.typing.typed (fmap nr_type_type Γ) e τ) :
      lam_halts (lam.contexts.fill_ctx uni_back_ctx e) <-> lamst_halts (lamst.contexts.fill_ctx C (embd_expr e)).
  Proof.
    split.
    - (* syn ≤ st *) intro SynHalt.
      eapply (uni_back_ctx_st_sem.uni_back_ctx_correct C); eauto.
      by rewrite -list_fmap_compose.
      eapply uni_back_ctx_sem_syn.uni_back_ctx_correct; eauto.
      replace (length Γ) with (length (nr_type_type <$> Γ)) by by rewrite fmap_length.
      eapply (uni_back_ctx_scoped C (nr_type_type <$> Γ)).
      by rewrite -list_fmap_compose.
      apply uni_back_ctx_sem_typed.
      by rewrite -list_fmap_compose.
    - (* st ≤ syn *) intro StHalt.
      eapply uni_back_ctx_sem_syn.uni_back_ctx_correct; eauto.
      replace (length Γ) with (length (nr_type_type <$> Γ)) by by rewrite fmap_length.
      eapply (uni_back_ctx_scoped C (nr_type_type <$> Γ)).
      by rewrite -list_fmap_compose.
      apply uni_back_ctx_sem_typed.
      by rewrite -list_fmap_compose.
      eapply (uni_back_ctx_st_sem.uni_back_ctx_correct C); eauto.
      by rewrite -list_fmap_compose.
  Qed.

End uni_back_ctx_st_syn.
