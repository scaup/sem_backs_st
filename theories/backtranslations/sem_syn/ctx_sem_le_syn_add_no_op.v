From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.

From st.prelude Require Import forall_three big_op_three.

From st.lam Require Import contexts lang contexts_subst nr_types scopedness types typing tactics.
From st.lam.logrel Require Import definitions fundamental generic.lift.

From st.backtranslations.un_syn Require Import expressions contexts universe.base.
From st.backtranslations.un_syn.logrel Require Import definitions un_le_syn.fundamental.

From st.backtranslations.sem_syn Require Import nr_embed_project nr_guard_assert nr_no_op connective.nr_un_le_syn gamma_lib.
From st Require Import resources.

Section sem_le_syn_S_n.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (s : stuckness) (Γ : list nr_type) (τr : nr_type).
  Context (pCsem : ctx_rel_typed s C C (map nr_type_type Γ) τr [] TUnit).

  Context (n : nat) (pn : length Γ = S n) (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).

  Context (e : expr) (pe : typed (map nr_type_type Γ) e τr).

  Definition C_wrapped_S_n : ctx :=
    let P : expr :=
        let filled_hole : expr :=
            ga_pair τr Guard (
                      wrap_funs_vars (Var (length Γ)) 0
                              ((fun τ => ga_pair τ Assert) <$> Γ)
                    )
        in
        fill_ctx C filled_hole
    in
    [CTX_LetInL (ga_pair NRTUnit Assert P)] ++ (LamGamma_ctx (length Γ)).

  Opaque ga_pair.

  Lemma rel_C_e_le_C_wrapped_S_n_e : ⊢ exprel_typed s TUnit (fill_ctx C e) (fill_ctx C_wrapped_S_n e).
  Proof.
    (* step *)
    iApply lift_step. simpl. rewrite -> pn at 1. rewrite fill_LamGamma_ctx. rewrite -LamGammaV_S_rw. auto_lam_step. iEval simplify_custom. change (Lam ?e) with (of_val (LamV e)). rewrite LamGammaV_S_rw -pn. rewrite ga_pair_Closed.
    (* assert 1 no op *)
    iApply (nr_no_op_ga_expr s NRTUnit).
    (* rewriting substitutions *)
    rewrite subst_fill_ctx. erewrite subst_closed_ctx; eauto. erewrite subst_closed_ctx_cont; eauto.
    (* using auto-relatedness of C *)
    unfold ctx_rel_typed in pCsem.
    assert (eq : ∀e, fill_ctx C e = (fill_ctx C e).[subst_list_val []]) by by asimpl.
    rewrite eq. rewrite (eq (ga_pair _ _ _).[_]). clear eq.
    iApply (pCsem); auto. iIntros (vs vs') "#Hvs". asimpl.
    rewrite ga_pair_Closed.
    (* some info for later *)
    iDestruct (big_sepL3_length with "Hvs") as "[%Hl1 %Hl2]".
    (* guard τr no op *)
    iApply (nr_no_op_ga_expr s τr).
    (* rewriting substitutions *)
    rewrite -subst_comp.
    rewrite wrap_funs_vars_subst1'. asimpl.
    rewrite (iter_up (length Γ) (length Γ)). destruct (lt_dec (length Γ) (length Γ)); first by lia. asimpl. rewrite Nat.sub_diag. asimpl.
    assert (Hc : Closed (LamGamma (length Γ) e)).
    { eapply expr_Closed_n, (expr_typed_scoped [] _ _).
      rewrite -fill_LamGamma_ctx. eapply typed_ctx_typed. apply pe.
      replace (length Γ) with (length (map nr_type_type Γ)).
      apply LamGamma_ctx_typed. by rewrite map_length.
    } rewrite Hc.
    rewrite wrap_funs_vars_subst2'.
    (* get some facts about the evaluation of our values *)
    rewrite -big_sepL3_fmap_l.
    iDestruct (big_sepL3_impl with "Hvs") as "Hvss".
    iAssert (□ (∀ (τ : nr_type) v v', valrel_typed s τ v v' -∗ (⌜ rtc lam_step (ga_pair τ Assert v') (nr_ga_eval τ Assert v') ⌝ ∧ valrel_typed s τ v (nr_ga_eval τ Assert v'))))%I as "H".
    iIntros (τ v v'). iModIntro. iIntros "#Hvv". by iApply nr_no_op_ga_help.
    iSpecialize ("Hvss" with "H"). iClear "H Hvs".
    iDestruct (big_sepL3_impl _ (fun τ _ v' => ⌜rtc lam_step (ga_pair τ Assert (of_val v')) (nr_ga_eval τ Assert v')⌝%I) with "Hvss") as "Hvs'".
    iDestruct (big_sepL3_pure with "[Hvs']") as "%Hvs'". iApply "Hvs'". iIntros (τ v v'). iModIntro. by iIntros "[H1 H2]". iClear "Hvs'".
    (* eval right side *)
    iApply lift_rtc_steps. apply (wrap_funs_vals_eval' (fmap (fun τv => nr_ga_eval τv.1 Assert τv.2) (zip Γ vs'))).
    by rewrite fmap_length. apply Forall_fmap. apply Forall_true. intro τ. apply ga_pair_Closed.
    rewrite Forall3_fmap_l Forall3_fmap_r. apply Forall3_superfluous_zip_r. simpl.
    by eapply Forall3_superfluous_m.
    (* using relatedness of e *)
    iApply (auto_related_typed_expr _ _ _ _ pe).
    rewrite -big_sepL3_fmap_l -big_sepL3_fmap_r. iApply big_sepL3_superfluous_zip_r_l. simpl.
    iApply (big_sepL3_impl with "Hvss"). iModIntro. by iIntros (τ v v') "[H1 H2]".
    (* easy remaining goals *)
    auto. rewrite fmap_length in Hl1. by rewrite fmap_length Hl1.
    apply Forall_fmap, Forall_true; intro τ; by apply ga_pair_Closed.
    apply Forall_fmap, Forall_true; intro τ; by apply ga_pair_Closed.
    by rewrite fmap_length.
  Qed.

End sem_le_syn_S_n.

Section sem_le_syn_0.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (s : stuckness) (τr : nr_type).
  Context (pCsem : ctx_rel_typed s C C [] τr [] TUnit).

  Context (pCscp : |sC> 0 ⊢ₙₒ C ☾ 0 ☽).

  Context (e : expr) (pe : typed [] e τr).

  Definition C_wrapped_0 : ctx :=
    [CTX_AppR (ga_pair NRTUnit Assert)] ++ C ++ [CTX_AppR (ga_pair τr Guard)].

  Opaque ga_pair.

  Lemma rel_C_e_le_C_wrapped_0_e : ⊢ exprel_typed s TUnit (fill_ctx C e) (fill_ctx C_wrapped_0 e).
  Proof.
    rewrite /= -fill_ctx_app.
    iApply (nr_no_op_ga_expr s NRTUnit).
    (* using auto-relatedness of C *)
    unfold ctx_rel_typed in pCsem.
    assert (eq : ∀e, fill_ctx C e = (fill_ctx C e).[subst_list_val []]) by by asimpl.
    rewrite eq. rewrite (eq (fill_ctx [CTX_AppR (ga_pair τr Guard)] e)).
    iApply (pCsem); auto. iIntros (vs vs') "#Hvs". asimpl.
    (* destruct vs; destruct vs'; auto. asimpl. *)
    (* no op *)
    rewrite ga_pair_Closed.
    iApply (nr_no_op_ga_expr s τr).
    (* using relatedness of e *)
    iApply (auto_related_typed_expr _ _ _ _ pe). auto.
  Qed.

End sem_le_syn_0.
