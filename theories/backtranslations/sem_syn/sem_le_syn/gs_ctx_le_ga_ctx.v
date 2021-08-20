From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.

From st.prelude Require Import forall_three big_op_three.

From st.STLCmuVS Require Import contexts lang contexts_subst types scopedness types typing tactics.
From st.STLCmuVS.logrel Require Import definitions fundamental generic.lift compat_lemmas.

From st.backtranslations.sem_syn Require Import gamma_lib.
From st.backtranslations.sem_syn.sem_le_syn Require Import guard_assert ga_ctx gs_ctx ghost_step_ga.

From st Require Import resources.

Opaque ga_pair.

Section gs_ctx_le_ga_ctx_0.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (τ : type) (pτ : Closed τ).

  Context (C : ctx) (pC : ctx_rel_typed MaybeStuck C C [] τ [] TUnit).

  Lemma rel_gs_ctx_le_ga_ctx_0 :
    ctx_rel_typed MaybeStuck (gs_ctx_nil C) (ga_ctx_nil C τ) [] τ [] TUnit.
  Proof.
    iIntros (e e' pe pe' Hee').
    apply open_exprel_typed_nil. simpl.
    iApply VirtStep_ga_expr. by intro σ; asimpl.
    rewrite -!fill_ctx_app.
    iApply open_exprel_typed_nil'. simpl.
    apply pC. by constructor. constructor; auto.
    apply expr_Closed_n. simpl. by apply ga_pair_closed.
    apply open_exprel_typed_nil.
    iApply VirtStep_ga_expr; auto.
    by iApply open_exprel_typed_nil'.
  Qed.

End gs_ctx_le_ga_ctx_0.

Section gs_ctx_le_ga_ctx_S_n.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (Γ : list type) (τ : type) (pΓ : Forall Closed Γ) (pτ : Closed τ).

  Context (n : nat) (pn : length Γ = S n).

  Context (C : ctx) (pC : ctx_rel_typed MaybeStuck C C Γ τ [] TUnit).

  Lemma wrap_funs_vals_help (Γ' : list type) :
    ∀ (HCΓ' : Forall Closed Γ') (F F' : expr) vs vs' (Hl : length vs = length Γ'),
      ⊢ exprel_typed MaybeStuck (GammaType Γ' τ) F F' -∗ (big_sepL3 (fun τ v v' => valrel_typed MaybeStuck τ v v') Γ' vs vs' ) -∗
        exprel_typed MaybeStuck τ
          (wrap_funs_vals F (zip (replicate (length Γ') (LamV (VirtStep (Var 0)))) vs))
          (wrap_funs_vals F' (zip ((λ τ : type, ga_pair Assert τ) <$> Γ') vs')).
  Proof.
    induction Γ' as [|τn Γ' IHΓ'] using rev_ind.
    - iIntros (HCΓ' F F' vs vs' Hl) "HF Hlist". destruct vs;[|inversion Hl].
      iDestruct (big_sepL3_length with "Hlist") as "[%Hl' %Hl'']". destruct vs';[|inversion Hl'']. simpl.
      rewrite /GammaType /=. iApply "HF".
    - iIntros (HCΓ' F F' vs vs' Hl) "HF Hlist".
      destruct (iffLR (Forall_app _ _ _) HCΓ') as [HC1 HC2].
      iDestruct (big_sepL3_length with "Hlist") as "[%Hl' %Hl'']".
      destruct vs as [|v vs _] using rev_ind. { exfalso. rewrite /= app_length /= in Hl. lia. }
      destruct vs' as [|v' vs' _] using rev_ind. { exfalso. rewrite /= app_length /= in Hl''. lia. }
      iDestruct (big_sepL3_app_inv with "Hlist") as "[#Hlist' #Hvv']"; auto; rewrite big_sepL3_singleton. iClear "Hlist".
      rewrite !app_length /= in Hl, Hl', Hl''.
      (* okay; eliminating one *)
      iEval (rewrite app_length !fmap_app /= !zip_snoc; try rewrite fmap_length; try lia).
      iEval (rewrite replicate_plus /=). rewrite zip_snoc; try by (rewrite replicate_length; lia).
      rewrite !wrap_funs_vals_snoc.
      rewrite !wrap_funs_vals_rw !fill_AppGamma_ectx.
      iApply (lift_bind with "[HF Hvv']").
      iApply (lift_bind _ [AppLCtx _] [AppLCtx _] with "HF").
      iIntros (f f') "#Hff". simpl.
      iApply (lift_bind _ [AppRCtx _] [AppRCtx _]).
      iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom. iApply VirtStep_ga_expr. by inversion HC2.
      by iApply lift_val.
      iIntros (w w') "Hww".
      simpl. rewrite -GammaType_snoc valrel_typed_TArrow_unfold. by iApply "Hff".
      setoid_rewrite <- fill_AppGamma_ectx.
      setoid_rewrite <- wrap_funs_vals_rw.
      (* using induction *)
      iIntros (f f') "#Hff".
      iApply (IHΓ' HC1 (of_val f) (of_val f') vs vs' ltac:(lia)); auto.
      by iApply lift_val.
  Qed.

  Context (psC : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).

  Lemma rel_gs_ctx_le_ga_ctx_S_n :
    ctx_rel_typed MaybeStuck (gs_ctx_cons C (length Γ)) (ga_ctx_cons C Γ τ) Γ τ [] TUnit.
  Proof.
    assert (HFC : Forall (fun f => Closed (of_val f)) (replicate (length Γ) (LamV (VirtStep (%0)%Eₙₒ)))).
    apply Forall_replicate. intro σ'; by asimpl.
    (* assert (H : |sC> 0 ⊢ₙₒ universe_back_ctx C ☾ length Γ ☽). *)
    (* { change 0 with (length (replicate 0 TUniverse)). rewrite pn. *)
    (*   replace (S n) with (length (replicate (S n) TUniverse)) by by rewrite replicate_length. *)
    (*   eapply ctx_typed_scoped, universe_back_ctx_typed. by rewrite -pn. } *)
    iIntros (e e' pe pe' Hee'). simpl. apply open_exprel_typed_nil.
    (* two steps *)
    Opaque LamGammaV_S.
    rewrite !pn !fill_LamGamma_ctx -!LamGammaV_S_rw -!pn.
    iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
    change (Lam (LamGamma n ?e)) with (LamGamma (S n) e). rewrite !pn -!LamGammaV_S_rw -!pn.
    iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
    change (Lam (LamGamma n ?e)) with (LamGamma (S n) e). rewrite !pn -!LamGammaV_S_rw -!pn.
    rewrite ga_pair_closed; try by intro σ; asimpl.
    (* connective lemma *)
    iApply VirtStep_ga_expr; first by intro σ; asimpl. iNext.
    (* rewriting substitutions *)
    rewrite !subst_fill_ctx. erewrite !(subst_closed_ctx _ _ (length Γ)); eauto. erewrite !(subst_closed_ctx_cont _ _ (length Γ)); eauto. simpl.
    rewrite ga_pair_closed; auto; try by intro σ; asimpl.
    (* using auto-relatedness of C *)
    iApply open_exprel_typed_nil'.
    apply pC; auto.
    { repeat constructor.
      rewrite wrap_funs_vars_subst1'; auto; try by rewrite replicate_length.
      asimpl. rewrite !(iter_up (length Γ) (length Γ)). destruct (lt_dec (length Γ) (length Γ)); first by lia.
      rewrite Nat.sub_diag. asimpl. rewrite LamGammaV_S_rw.
      rewrite -pn.
      replace (ren (+ (length Γ)) : Ids expr) with (upn 0 (ren (+ (length Γ))) : Ids expr) by by asimpl.
      rewrite (iffRL (expr_Closed_n _ _) (LamGamma_scoped _ _ pe)).
      apply expr_Closed_n. intro σ.
      rewrite wrap_funs_vars_subst1'; auto; try by rewrite replicate_length.
      by rewrite (iffRL (expr_Closed_n _ _) (LamGamma_scoped _ _ pe)).
    }
    { repeat constructor.
      apply expr_Closed_n. intro σ. by rewrite ga_pair_closed.
      rewrite wrap_funs_vars_subst1'; auto; try by rewrite replicate_length.
      asimpl. rewrite !(iter_up (length Γ) (length Γ)). destruct (lt_dec (length Γ) (length Γ)); first by lia.
      rewrite Nat.sub_diag. asimpl. rewrite LamGammaV_S_rw.
      rewrite -pn.
      replace (ren (+ (length Γ)) : Ids expr) with (upn 0 (ren (+ (length Γ))) : Ids expr) by by asimpl.
      rewrite (iffRL (expr_Closed_n _ _) (LamGamma_scoped _ _ pe')).
      apply expr_Closed_n. intro σ.
      rewrite wrap_funs_vars_subst1'; auto; try by rewrite replicate_length.
      by rewrite (iffRL (expr_Closed_n _ _) (LamGamma_scoped _ _ pe')).
      all: try by rewrite fmap_length.
      all: eapply Forall_fmap, Forall_impl; eauto; intros; try by apply ga_pair_closed.
    }
    (* introducing stuff *)
    iIntros (vs vs') "#Hvs". simpl.
    rewrite ga_pair_closed; auto; try by intro σ; asimpl.
    (* collecting info *)
    iDestruct (big_sepL3_length with "Hvs") as "[%Hl' %Hll']".
    (* connective lemma *)
    iApply VirtStep_ga_expr; auto.
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
    by rewrite -Hll'.
    all: try by rewrite replicate_length.
    all: eapply Forall_fmap, Forall_impl; eauto.
    all: intros; try by apply ga_pair_closed.
  Qed.

End gs_ctx_le_ga_ctx_S_n.

Section gs_ctx_le_ga_ctx.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (Γ : list type) (τ : type) (pΓ : Forall Closed Γ) (pτ : Closed τ).

  Context (C : ctx) (pC : ctx_rel_typed MaybeStuck C C Γ τ [] TUnit).

  Context (psC : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).

  Lemma rel_gs_ctx_le_ga_ctx :
    ctx_rel_typed MaybeStuck (gs_ctx C (length Γ)) (ga_ctx C Γ τ) Γ τ [] TUnit.
  Proof.
    destruct (length Γ) eqn:eq.
    - destruct Γ; [|by inversion eq]. by apply rel_gs_ctx_le_ga_ctx_0.
    - rewrite /gs_ctx /ga_ctx. rewrite eq. rewrite -eq. eapply rel_gs_ctx_le_ga_ctx_S_n; eauto.
      by rewrite eq.
  Qed.

End gs_ctx_le_ga_ctx.
