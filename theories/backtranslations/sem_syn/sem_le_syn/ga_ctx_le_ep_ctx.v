From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.

From st.prelude Require Import forall_three big_op_three.

From st.lam Require Import contexts lang contexts_subst types scopedness types typing tactics.
From st.lam.logrel Require Import definitions fundamental generic.lift compat_lemmas.

From st.backtranslations.un_syn Require Import expressions contexts universe.base.
From st.backtranslations.un_syn.logrel Require Import definitions un_le_syn.fundamental.

From st.backtranslations.sem_syn Require Import embed_project gamma_lib back_ctx.
From st.backtranslations.sem_syn.sem_le_syn Require Import guard_assert ga_ctx connective.

From st Require Import resources.

Opaque ga_pair ep_pair.

Instance rfn : refinement := un_le_syn.

Section ga_ctx_le_ep_ctx_0.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (τ : type) (pτ : Closed τ).

  Context (pCscp : |sC> 0 ⊢ₙₒ C ☾ 0 ☽).

  Lemma rel_ga_ctx_le_ep_ctx_0 :
    ctx_rel_typed MaybeStuck (ga_ctx_nil C τ) (back_ctx_nil C τ) [] τ [] TUnit.
  Proof.
    iIntros (e e' pe pe' Hee').
    apply open_exprel_typed_nil. simpl.
    iApply assert_project_connective_expr. by intro σ; asimpl.
    rewrite -!fill_ctx_app.
    iApply open_exprel_nil'. simpl.
    apply (universe_back_ctx_in_relation 0 0 C pCscp).
    apply open_exprel_nil.
    iApply guard_embed_connective_expr. auto.
    by iApply open_exprel_typed_nil'.
  Qed.

End ga_ctx_le_ep_ctx_0.

Section ga_ctx_le_ep_ctx_S_n.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (Γ : list type) (τ : type).
  Context (n : nat) (pn : length Γ = S n) (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).

  Lemma wrap_funs_vals_help (Γ' : list type) :
    ∀ (HCΓ' : Forall Closed Γ') (F F' : expr) vs vs' (Hl : length vs = length Γ'),
      ⊢ exprel_typed MaybeStuck (GammaType Γ' τ) F F' -∗ ([∗ list] v;v' ∈ vs;vs', valrel v v') -∗
        exprel_typed MaybeStuck τ
          (wrap_funs_vals F (zip ((λ τ : type, ga_pair Assert τ) <$> Γ') vs))
          (wrap_funs_vals F' (zip ((λ τ : type, ep_pair Project τ) <$> Γ') vs')).
  Proof.
    induction Γ' as [|τn Γ' IHΓ'] using rev_ind.
    - iIntros (HCΓ' F F' vs vs' Hl) "HF Hlist". destruct vs;[|inversion Hl].
      iDestruct (big_sepL2_length with "Hlist") as "%Hl'". destruct vs';[|inversion Hl']. simpl.
      rewrite /GammaType /=. iApply "HF".
    - iIntros (HCΓ' F F' vs vs' Hl) "HF Hlist".
      destruct (iffLR (Forall_app _ _ _) HCΓ') as [HC1 HC2].
      destruct vs as [|v vs _] using rev_ind. { exfalso. rewrite /= app_length /= in Hl. lia. }
      iDestruct (big_sepL2_app_inv_l with "Hlist") as (ws' w') "(-> & #Hlist & Hw)".
      iDestruct (big_sepL2_length with "Hw") as "%Hl''".
      destruct w' as [|w' rem _] using rev_ind. { exfalso. rewrite /= in Hl''. lia. }
      destruct rem as [|r rem _] using rev_ind; [|exfalso; rewrite /= !app_length /= in Hl''; lia ]. clear Hl''.
      iDestruct (big_sepL2_length with "Hlist") as "%Hl'". rewrite !app_length /= in Hl.
      rename w' into v', ws' into vs'. rewrite app_nil_l. iDestruct "Hw" as "[#Hw _]".
      (* okay; eliminating one *)
      rewrite !fmap_app /= !zip_snoc; try rewrite fmap_length; try lia.
      rewrite !wrap_funs_vals_snoc.
      rewrite !wrap_funs_vals_rw !fill_AppGamma_ectx.
      iApply (lift_bind with "[HF Hw]").
      iApply (lift_bind _ [AppLCtx _] [AppLCtx _] with "HF").
      iIntros (f f') "#Hff". simpl.
      iApply (lift_bind _ [AppRCtx _] [AppRCtx _]).
      iApply assert_project_connective; auto. by inversion HC2. iIntros (w w') "Hww".
      simpl. rewrite -GammaType_snoc valrel_typed_TArrow_unfold. by iApply "Hff".
      setoid_rewrite <- fill_AppGamma_ectx.
      setoid_rewrite <- wrap_funs_vals_rw.
      (* using induction *)
      iIntros (f f') "#Hff".
      iApply (IHΓ' HC1 (of_val f) (of_val f') vs vs' ltac:(lia)); auto.
      by iApply lift_val.
  Qed.

  Context (pΓ : Forall Closed Γ) (pτ : Closed τ).

  Lemma rel_ga_ctx_le_ep_ctx_S_n :
    ctx_rel_typed MaybeStuck (ga_ctx_cons C Γ τ) (back_ctx_cons C Γ τ) Γ τ [] TUnit.
  Proof.
    assert (H : |sC> 0 ⊢ₙₒ universe_back_ctx C ☾ length Γ ☽).
    { change 0 with (length (replicate 0 TUniverse)). rewrite pn.
      replace (S n) with (length (replicate (S n) TUniverse)) by by rewrite replicate_length.
      eapply ctx_typed_scoped, universe_back_ctx_typed. by rewrite -pn. }
    iIntros (e e' pe pe' Hee'). simpl. apply open_exprel_typed_nil.
    (* two steps *)
    Opaque LamGammaV_S.
    rewrite !pn !fill_LamGamma_ctx -!LamGammaV_S_rw -!pn.
    iApply lift_step. auto_lam_step. iEval simplify_custom.
    change (Lam (LamGamma n ?e)) with (LamGamma (S n) e). rewrite !pn -!LamGammaV_S_rw -!pn.
    iApply lift_step_later. auto_lam_step. iEval simplify_custom.
    change (Lam (LamGamma n ?e)) with (LamGamma (S n) e). rewrite !pn -!LamGammaV_S_rw -!pn.
    rewrite ga_pair_closed; try by intro σ; asimpl.
    rewrite ep_pair_Closed; try by intro σ; asimpl.
    (* connective lemma *)
    iApply assert_project_connective_expr; first by intro σ; asimpl. iNext.
    (* rewriting substitutions *)
    rewrite !subst_fill_ctx. erewrite !(subst_closed_ctx _ _ (length Γ)); eauto. erewrite !(subst_closed_ctx_cont _ _ (length Γ)); eauto. simpl.
    rewrite ga_pair_closed; auto; try by intro σ; asimpl.
    rewrite ep_pair_Closed; auto; try by intro σ; asimpl.
    (* using auto-relatedness of C *)
    iApply open_exprel_nil'.
    apply (universe_back_ctx_in_relation _ _ C pCscp); auto.
    (* introducing stuff *)
    iIntros (vs vs' Hl) "#Hvs". simpl.
    rewrite ga_pair_closed; auto; try by intro σ; asimpl.
    rewrite ep_pair_Closed; auto; try by intro σ; asimpl.
    (* collecting info *)
    iDestruct (big_sepL2_length with "Hvs") as "%Hl'".
    (* connective lemma *)
    iApply guard_embed_connective_expr; auto.
    (* rewriting substitutions *)
    rewrite !wrap_funs_vars_subst1'. asimpl.
    rewrite !(iter_up (length Γ) (length Γ)). destruct (lt_dec (length Γ) (length Γ)); first by lia. asimpl. rewrite Nat.sub_diag. asimpl.
    assert (Hc : Closed (LamGamma (length Γ) e)).
    { by apply expr_Closed_n, LamGamma_scoped. }
    assert (Hc' : Closed (LamGamma (length Γ) e')).
    { by apply expr_Closed_n, LamGamma_scoped. }
    rewrite !LamGammaV_S_rw.
    replace (ren (+length Γ) : Ids expr) with (upn 0 (ren (+length Γ) : Ids expr)) by by asimpl.
    rewrite -!pn Hc Hc'.
    (* !pn -!LamGammaV_S_rw. *)
    rewrite !wrap_funs_vars_subst2'; auto.
    iApply wrap_funs_vals_help; eauto.
    (* ok *)
    iApply open_exprel_typed_nil'.
    rewrite -!fill_LamGamma_ctx.
    eapply (auto_related_ctx_typed _ _ _ _ _ (LamGamma_ctx (length Γ))).
    apply LamGamma_ctx_typed.
    (* remaining goals *)
    all:auto. all: try rewrite fmap_length; try done.
    by rewrite -Hl'.
    all: eapply Forall_fmap, Forall_impl; eauto.
    all: intros; try by apply ep_pair_Closed.
    all: intros; try by apply ga_pair_closed.
  Qed.

End ga_ctx_le_ep_ctx_S_n.

Section ga_ctx_le_ep_ctx.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (Γ : list type) (τ : type).
  Context (pΓ : Forall Closed Γ) (pτ : Closed τ).

  Context (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).

  Lemma rel_ga_ctx_le_ep_ctx :
    ctx_rel_typed MaybeStuck (ga_ctx C Γ τ) (back_ctx C Γ τ) Γ τ [] TUnit.
  Proof.
    destruct (length Γ) eqn:eq.
    - destruct Γ; [|by inversion eq]. by apply rel_ga_ctx_le_ep_ctx_0.
    - rewrite /back_ctx /ga_ctx. rewrite eq. eapply rel_ga_ctx_le_ep_ctx_S_n; eauto.
      by rewrite eq.
  Qed.

End ga_ctx_le_ep_ctx.
