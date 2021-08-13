From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.

From st.prelude Require Import forall_three big_op_three.

From st.lam Require Import contexts lang contexts_subst types scopedness types typing tactics ghost_steps.
From st.lam.logrel Require Import definitions fundamental generic.lift.

From st.backtranslations.sem_syn.sem_le_syn Require Import no_op gs_ctx.
From st.backtranslations.sem_syn Require Import gamma_lib.

From st Require Import resources.

Section ctx_le_gs_ctx_0.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (τ : type).
  Context (pCsem : ctx_rel_typed MaybeStuck C C [] τ [] TUnit).

  Context (pCscp : |sC> 0 ⊢ₙₒ C ☾ 0 ☽).

  Lemma rel_ctx_le_gs_ctx_0 :
    ctx_rel_typed MaybeStuck C (gs_ctx_nil C) [] τ [] TUnit.
  Proof.
    iIntros (e e' pe pe' Hee').
    apply open_exprel_typed_nil.
    rewrite -fill_ctx_app /=.
    iApply GhostStep_no_op_expr.
    iApply open_exprel_typed_nil'.
    rewrite -fill_ctx_app /=.
    apply pCsem; auto. by constructor.
    apply open_exprel_typed_nil.
    iApply GhostStep_no_op_expr.
    by iApply open_exprel_typed_nil'.
  Qed.

End ctx_le_gs_ctx_0.

Section ctx_le_gs_ctx_S_n.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (Γ : list type) (τ : type).
  Context (pCsem : ctx_rel_typed MaybeStuck C C Γ τ [] TUnit).

  Context (n : nat) (pn : length Γ = S n) (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).

  Lemma rel_ctx_le_gs_ctx_S_n : ctx_rel_typed MaybeStuck C (gs_ctx_cons C (length Γ)) Γ τ [] TUnit.
  Proof.
    assert (HFC : Forall (fun f => Closed (of_val f)) (replicate (length Γ) (LamV (GhostStep (%0)%Eₙₒ)))).
    apply Forall_replicate. intro σ'; by asimpl.
    iIntros (e e' pe pe' Hee').
    apply open_exprel_typed_nil.
    (* step *)
    Opaque LamGammaV_S.
    iApply lift_step. simpl. rewrite fill_LamGamma_ctx. rewrite -> pn at 1. rewrite -LamGammaV_S_rw. auto_lam_step.
    simplify_custom.
    replace (Lam (LamGamma n e')) with (LamGamma (S n) e'); auto. rewrite -LamGammaV_S_rw.
    (* no op *)
    iApply GhostStep_no_op_expr.
    (* rewriting substitutions *)
    rewrite subst_fill_ctx. erewrite subst_closed_ctx; eauto. erewrite subst_closed_ctx_cont; eauto.
    (* using auto-relatedness of C *)
    iApply open_exprel_typed_nil'. apply pCsem; auto.
    { repeat constructor.
      rewrite wrap_funs_vars_subst1'; auto; try by rewrite replicate_length.
      asimpl. rewrite !(iter_up (length Γ) (length Γ)). destruct (lt_dec (length Γ) (length Γ)); first by lia.
      rewrite Nat.sub_diag. asimpl. rewrite LamGammaV_S_rw.
      rewrite -pn.
      replace (ren (+ (length Γ)) : Ids expr) with (upn 0 (ren (+ (length Γ))) : Ids expr) by by asimpl.
      rewrite (iffRL (expr_Closed_n _ _) (LamGamma_scoped _ _ pe')).
      apply expr_Closed_n. intro σ.
      rewrite wrap_funs_vars_subst1'; auto; try by rewrite replicate_length.
      by rewrite (iffRL (expr_Closed_n _ _) (LamGamma_scoped _ _ pe')).
    }
    asimpl.
    iIntros (vs vs') "#Hvsvs'". simpl.
    iApply GhostStep_no_op_expr.
    rewrite wrap_funs_vars_subst1'; auto; try by rewrite replicate_length.
    asimpl. rewrite !(iter_up (length Γ) (length Γ)). destruct (lt_dec (length Γ) (length Γ)); first by lia.
    rewrite Nat.sub_diag. asimpl. rewrite LamGammaV_S_rw.
    rewrite -pn.
    replace (ren (+ (length Γ)) : Ids expr) with (upn 0 (ren (+ (length Γ))) : Ids expr) by by asimpl.
    rewrite (iffRL (expr_Closed_n _ _) (LamGamma_scoped _ _ pe')).
    (* some facts about our lists *)
    iDestruct (big_sepL3_length with "Hvsvs'") as "[%Hl1 %Hl2]".
    iAssert (big_sepL3 (λ (τ0 : definitions.typeO) (v v' : valO),
                  valrel_typed MaybeStuck τ0 v v') Γ vs (fmap GhostStepped vs')) as "Hvsvs''".
    rewrite -big_sepL3_fmap_r.
    iApply (big_sepL3_impl with "Hvsvs'"). iModIntro. iIntros (τ' v v') "#Hvv'".
    by iApply GhostStep_no_op_help. iClear "Hvsvs'".
    (* eval *)
    rewrite wrap_funs_vars_subst2'; auto; try by rewrite replicate_length -Hl2 -Hl1. 2: by apply expr_Closed_n, LamGamma_scoped.
    (* eval right side *)
    iApply lift_rtc_steps. apply (wrap_funs_vals_eval' (fmap GhostStepped vs')).
    by rewrite replicate_length. auto.
    rewrite Forall3_fmap_r. replace (replicate (length Γ) (LamV (GhostStep (%0)%Eₙₒ))) with (fmap (fun _ => (LamV (GhostStep (%0)%Eₙₒ))) vs').
    rewrite Forall3_fmap_l. apply Forall3_same. apply Forall_true.
    intros. simpl. eapply rtc_l. auto_lam_step. simplify_custom. apply GhostStep_eval.
    erewrite const_fmap. rewrite -Hl2 -Hl1. done. auto.
    by iApply Hee'.
  Qed.

End ctx_le_gs_ctx_S_n.

Section ctx_le_gs_ctx.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (Γ : list type) (τ : type).
  Context (pCsem : ctx_rel_typed MaybeStuck C C Γ τ [] TUnit).

  Context (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).

  Lemma rel_ctx_le_gs_ctx : ctx_rel_typed MaybeStuck C (gs_ctx C (length Γ)) Γ τ [] TUnit.
  Proof.
    destruct (length Γ) eqn:eq.
    - destruct Γ; [|by inversion eq]. by apply rel_ctx_le_gs_ctx_0.
    - rewrite /gs_ctx -eq. eapply rel_ctx_le_gs_ctx_S_n; eauto.
      by rewrite eq.
  Qed.

End ctx_le_gs_ctx.
