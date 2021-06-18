From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.

From st.prelude Require Import forall_three big_op_three.

From st.lam Require Import contexts lang contexts_subst nr_types scopedness types typing tactics.
From st.lam.logrel Require Import definitions fundamental generic.lift compat_lemmas.

From st.backtranslations.un_syn Require Import expressions contexts universe.base.
From st.backtranslations.un_syn.logrel Require Import definitions un_le_syn.fundamental.

From st.backtranslations.sem_syn Require Import nr_embed_project nr_guard_assert nr_no_op connective.nr_un_le_syn gamma_lib uni_back_ctx ctx_sem_le_syn_add_no_op.
From st Require Import resources.

Opaque ga_pair ep_pair.

Instance rfn : refinement := un_le_syn.

Section un_le_syn_S_n.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (Γ : list nr_type) (τr : nr_type).
  Context (n : nat) (pn : length Γ = S n) (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).

  Context (e : expr) (pe : typed (map nr_type_type Γ) e τr).

  Lemma wrap_funs_vals_help (Γ' : list nr_type) :
    ∀ (F F' : expr) vs vs' (Hl : length vs = length Γ'),
      ⊢ exprel_typed MaybeStuck (GammaType (fmap nr_type_type Γ') τr) F F' -∗ ([∗ list] v;v' ∈ vs;vs', valrel v v') -∗
        exprel_typed MaybeStuck τr
          (wrap_funs_vals F (zip ((λ τ : nr_type, ga_pair τ Assert) <$> Γ') vs))
          (wrap_funs_vals F' (zip ((λ τ : nr_type, ep_pair τ Project) <$> Γ') vs')).
  Proof.
    induction Γ' as [|τn Γ' IHΓ'] using rev_ind.
    - iIntros (F F' vs vs' Hl) "HF Hlist". destruct vs;[|inversion Hl].
      iDestruct (big_sepL2_length with "Hlist") as "%Hl'". destruct vs';[|inversion Hl']. simpl.
      rewrite /GammaType /=. iApply "HF".
    - iIntros (F F' vs vs' Hl) "HF Hlist".
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
      iApply nr_assert_project_connective; auto. iIntros (w w') "Hww".
      simpl. rewrite -GammaType_snoc valrel_typed_TArrow_unfold. by iApply "Hff".
      setoid_rewrite <- fill_AppGamma_ectx.
      setoid_rewrite <- wrap_funs_vals_rw.
      (* using induction *)
      iIntros (f f') "#Hff".
      iApply (IHΓ' (of_val f) (of_val f') vs vs' ltac:(lia)); auto.
      by iApply lift_val.
  Qed.

  Lemma rel_C_wrapped_S_n_e_le_uni_back_ctx_cons_e :
    ⊢ exprel_typed s TUnit (fill_ctx (C_wrapped_S_n C Γ τr) e) (fill_ctx (uni_back_ctx_cons C Γ τr) e) .
  Proof.
    assert (H : |sC> 0 ⊢ₙₒ back_ctx C ☾ length Γ ☽).
    { change 0 with (length ([] : list type)).
      replace (length Γ) with (length (replicate (length Γ) TUniverse)).
      eapply (ctx_typed_scoped (replicate (length Γ) TUniverse) TUniverse []).
      change [] with (replicate 0 TUniverse).
        by apply back_ctx_typed. by rewrite replicate_length. }
    simpl.
    (* two steps *)
    iApply lift_step. rewrite -> pn at 1. rewrite fill_LamGamma_ctx. rewrite -LamGammaV_S_rw. auto_lam_step. iEval simplify_custom. change (Lam ?e) with (of_val (LamV e)). rewrite LamGammaV_S_rw -pn. rewrite ep_pair_Closed.
    iApply lift_step_later. rewrite -> pn at 1. rewrite fill_LamGamma_ctx. rewrite -LamGammaV_S_rw. auto_lam_step. iEval simplify_custom. change (Lam ?e) with (of_val (LamV e)). rewrite LamGammaV_S_rw -pn. rewrite ga_pair_Closed. iNext.
    (* connective lemma *)
    iApply (nr_assert_project_connective_expr NRTUnit).
    (* rewriting substitutions *)
    rewrite !subst_fill_ctx. erewrite !(subst_closed_ctx _ _ (length Γ)); eauto. erewrite !(subst_closed_ctx_cont _ _ (length Γ)); eauto. simpl.
    rewrite ga_pair_Closed ep_pair_Closed.
    (* using auto-relatedness of C *)
    assert (eq : ∀C e, fill_ctx C e = (fill_ctx C e).[subst_list_val []]) by by asimpl.
    rewrite (eq C) (eq (back_ctx C)).
    iApply (back_ctx_in_relation _ _ C pCscp); auto.
    (* introducing stuff *)
    iIntros (vs vs' Hl) "#Hvs". simpl. rewrite ga_pair_Closed ep_pair_Closed.
    (* collecting info *)
    iDestruct (big_sepL2_length with "Hvs") as "%Hl'".
    (* connective lemma *)
    iApply (nr_guard_embed_connective_expr τr).
    (* rewriting substitutions *)
    rewrite !wrap_funs_vars_subst1'. asimpl.
    rewrite !(iter_up (length Γ) (length Γ)). destruct (lt_dec (length Γ) (length Γ)); first by lia. asimpl. rewrite Nat.sub_diag. asimpl.
    assert (Ht : typed [] (LamGamma (length Γ) e) (GammaType (fmap nr_type_type Γ) τr)).
    { rewrite -(fmap_length nr_type_type).
      by eapply LamGamma_typed. }
    assert (Hc : Closed (LamGamma (length Γ) e)).
    { eapply expr_Closed_n, (expr_typed_scoped [] _ _).
      apply Ht. } rewrite Hc.
    rewrite !wrap_funs_vars_subst2'.
    iApply wrap_funs_vals_help; eauto.
    replace (LamGamma (length Γ) e) with (LamGamma (length Γ) e).[subst_list_val []] by by asimpl.
    iApply auto_related_typed_expr.
    apply Ht. auto.
    (* remaining goals *)
    all: auto; try rewrite fmap_length; try lia. by rewrite -Hl Hl'.
    1-4: by apply Forall_fmap, Forall_true; intros τ σ; (rewrite ep_pair_Closed || rewrite ga_pair_Closed).
  Qed.

End un_le_syn_S_n.

Section un_le_syn_0.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (τr : nr_type).

  Context (pCscp : |sC> 0 ⊢ₙₒ C ☾ 0 ☽).

  Context (e : expr) (pe : typed [] e τr).

  Lemma rel_C_wrapped_0_e_le_uni_back_ctx_nil_e :
    ⊢ exprel_typed s TUnit (fill_ctx (C_wrapped_0 C τr) e) (fill_ctx (uni_back_ctx_nil C τr) e) .
  Proof.
    simpl.
    iApply (nr_assert_project_connective_expr NRTUnit).
    rewrite -!fill_ctx_app.
    assert (eq : ∀C e, fill_ctx C e = (fill_ctx C e).[subst_list_val []]) by by asimpl.
    rewrite (eq C) (eq (back_ctx C)). iApply (back_ctx_in_relation 0 0 C pCscp); eauto.
    simpl.
    iIntros (vs vs' Hl) "Hvs". simpl. rewrite ga_pair_Closed ep_pair_Closed.
    iApply (nr_guard_embed_connective_expr τr).
    iApply auto_related_typed_expr; eauto. destruct vs; destruct vs'; auto.
  Qed.

End un_le_syn_0.
