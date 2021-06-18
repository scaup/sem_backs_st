From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.lam Require Import types lang wkpre generic.lift logrel.definitions contexts.
From st.backtranslations.st_sem Require Import ghost heap_emul.base.
From st.backtranslations.st_sem.well_defined.logrel Require Import definition.
From st Require Import embedding.types.
From st Require Import prelude.big_op_three.
From st Require Import resources.

(* Given any non-st type, the two relations agree. *)

Section matches_sem_val.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (Δ : list gname).

  Notation valrel_sem_typed := (lam.logrel.definitions.valrel_typed MaybeStuck).
  Notation valrel_st_typed := (well_defined.logrel.definition.valrel_typed Δ).

  Lemma matches_sem : ∀ (τ : type) (v v' : val) , valrel_sem_typed τ v v' ⊣⊢ valrel_st_typed [|τ|] v v'.
  Proof.
    iLöb as "IHlob".
    iIntros (τ). iInduction τ as [ | | | τ1 τ2 | τ1 τ2 | τ1 τ2 | τb | ] "IH".
    - setoid_rewrite valrel_typed_TUnit_unfold.
      setoid_rewrite lam.logrel.definitions.valrel_typed_TUnit_unfold.
      auto.
    - setoid_rewrite valrel_typed_TBool_unfold.
      setoid_rewrite lam.logrel.definitions.valrel_typed_TBool_unfold.
      auto.
    - setoid_rewrite valrel_typed_TInt_unfold.
      setoid_rewrite lam.logrel.definitions.valrel_typed_TInt_unfold.
      auto.
    - setoid_rewrite valrel_typed_TProd_unfold. fold embed.
      setoid_rewrite lam.logrel.definitions.valrel_typed_TProd_unfold.
      iIntros (v v').
      iSplit.
      + iIntros "Hdes". iDestruct "Hdes" as (v1 v2 v1' v2') "(eq1 & eq2 & H1 & H2)".
        repeat iExists _. repeat iSplit; auto. by iApply "IH". by iApply "IH1".
      + iIntros "Hdes". iDestruct "Hdes" as (v1 v2 v1' v2') "(eq1 & eq2 & H1 & H2)".
        repeat iExists _. repeat iSplit; auto. by iApply "IH". by iApply "IH1".
    - setoid_rewrite valrel_typed_TSum_unfold. fold embed.
      setoid_rewrite lam.logrel.definitions.valrel_typed_TSum_unfold.
      iIntros (v v').
      iSplit.
      + iIntros "Hdes". iDestruct "Hdes" as (v1 v1') "[(eq1 & eq2 & H) | (eq1 & eq2 & H)]".
        * repeat iExists _. iLeft. repeat iSplit; eauto. by iApply "IH".
        * repeat iExists _. iRight. repeat iSplit; eauto. by iApply "IH1".
      + iIntros "Hdes". iDestruct "Hdes" as (v1 v1') "[(eq1 & eq2 & H) | (eq1 & eq2 & H)]".
        * repeat iExists _. iLeft. repeat iSplit; eauto. by iApply "IH".
        * repeat iExists _. iRight. repeat iSplit; eauto. by iApply "IH1".
    - setoid_rewrite valrel_typed_TArrow_unfold. fold embed.
      setoid_rewrite lam.logrel.definitions.valrel_typed_TArrow_unfold.
      iIntros (w w'). iSplit.
      + iIntros "#H". iModIntro. iIntros (v v') "#H1".
        iApply (lift_wand _ (valrel_sem_typed τ3)). iIntros (x x') "Hxx'". by iApply "IH1".
        iApply "H". by iApply "IH".
      + iIntros "#H". iModIntro. iIntros (v v') "#H1".
        iApply (lift_wand _ (valrel_st_typed [|τ3|])). iIntros (x x') "Hxx'". by iApply "IH1".
        iApply "H". by iApply "IH".
    - setoid_rewrite valrel_typed_TRec_unfold. fold embed.
      rewrite -embed_TRec_comm.
      setoid_rewrite lam.logrel.definitions.valrel_typed_TRec_unfold.
      iIntros (v v'). iSplit.
      + iIntros "Hdes". iDestruct "Hdes" as (w w') "(eq & eq' & H)".
        iExists w, w'. repeat iSplit; auto. iNext. by iApply "IHlob".
      + iIntros "Hdes". iDestruct "Hdes" as (w w') "(eq & eq' & H)".
        iExists w, w'. repeat iSplit; auto. iNext. by iApply "IHlob".
    - setoid_rewrite valrel_typed_TVar_unfold.
      setoid_rewrite lam.logrel.definitions.valrel_typed_TVar_unfold. auto.
  Qed.

End matches_sem_val.

Section matches_sem_expr.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (Δ : list gname).

  Notation exprel_sem_typed := (lam.logrel.definitions.exprel_typed MaybeStuck).
  Notation exprel_st_typed := (well_defined.logrel.definition.exprel_typed Δ).

  Lemma matches_sem_expr : ∀ (τ : type) (e e' : expr) , exprel_sem_typed τ e e' ⊣⊢ exprel_st_typed [|τ|] e e'.
  Proof. intros τ e e'. apply lift_equiv. apply matches_sem. Qed.

End matches_sem_expr.

Section matches_sem_expr_open.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Notation open_exprel_sem_typed := (lam.logrel.definitions.open_exprel_typed MaybeStuck).
  Notation open_exprel_st_typed := (well_defined.logrel.definition.open_exprel_typed).

  Lemma matches_sem_open_expr Γ τ e e' : open_exprel_sem_typed Γ e e' τ <-> open_exprel_st_typed (embed <$> Γ) e e' [|τ|].
  Proof.
    split.
    - intro Hsem. iIntros (Δ vs vs') "Hvsvs'".
      iApply matches_sem_expr.
      iApply Hsem.
      iApply (big_sepL3_impl with "[Hvsvs']").
      iApply (big_sepL3_fmap_l with "Hvsvs'").
      iModIntro. iIntros (τ' v v') "H". by iApply matches_sem.
    - intro Hsem. iIntros (vs vs') "Hvsvs'".
      iApply (matches_sem_expr []).
      iApply Hsem.
      iApply (big_sepL3_fmap_l).
      iApply (big_sepL3_impl with "Hvsvs'").
      iModIntro. iIntros (τ' v v') "H". by iApply matches_sem.
  Qed.

End matches_sem_expr_open.

Section matches_sem_ctx.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Notation ctx_item_sem_typed := (lam.logrel.definitions.ctx_item_rel_typed MaybeStuck).
  Notation ctx_sem_typed := (lam.logrel.definitions.ctx_rel_typed MaybeStuck).

  Notation ctx_item_rel_st_typed := (well_defined.logrel.definition.ctx_item_rel_typed).
  Notation ctx_rel_st_typed := (well_defined.logrel.definition.ctx_rel_typed).

  Lemma matches_sem_ctx C C' Γ τ Γ' τ' :
    ctx_sem_typed C C' Γ τ Γ' τ' <-> ctx_rel_st_typed C C' (embed <$> Γ) [|τ|] (embed <$> Γ') [|τ'|].
  Proof.
    split; intros H e e' Hee'.
    - apply matches_sem_open_expr. apply H.
      by apply matches_sem_open_expr.
    - apply matches_sem_open_expr. apply H.
      by apply matches_sem_open_expr.
  Qed.

End matches_sem_ctx.
