From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.

From st.prelude Require Import forall_three big_op_three.

From st.STLCmuVS Require Import contexts lang contexts_subst scopedness typing tactics.
From st.STLCmu Require Import types.
From st.STLCmuVS.logrel Require Import definitions fundamental generic.lift compat_lemmas.

From st.backtranslations.un_syn Require Import expressions contexts universe.base.
From st.backtranslations.un_syn.logrel Require Import definitions syn_le_un.fundamental.

From st.backtranslations.sem_syn Require Import embed_project gamma_lib back_ctx.
From st.backtranslations.sem_syn.syn_le_sem Require Import connective.
From st Require Import resources.

Opaque ep_pair.

Instance rfn : refinement := syn_le_un.

Section syn_le_un_0.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (C : ctx).

  Context (τ : type) (pτ : Closed τ).
  Context (pCscp : |sC> 0 ⊢ₙₒ C ☾ 0 ☽).

  Lemma rel_back_ctx_nil :
    ctx_rel_typed MaybeStuck (back_ctx_nil C τ) C [] τ [] TUnit.
  Proof.
    iIntros (e e' pe pe' Hee'). simpl. apply open_exprel_typed_nil.
    iApply project_connective_expr. by intro σ; asimpl. simpl.
    rewrite -!fill_ctx_app. iApply open_exprel_nil'.
    apply (universe_back_ctx_in_relation 0 0 C pCscp). simpl.
    apply open_exprel_nil.
    iApply embed_connective_expr; auto. by iApply open_exprel_typed_nil'.
  Qed.

End syn_le_un_0.

Section syn_le_un_S_n.

  Context (Γ : list type).

  Lemma subst_list_val_anti_steps e vs (Hl : length vs = length Γ) :
    rtc STLCmuVS_step (wrap_funs_vals (LamGamma (length Γ) e) (zip (replicate (length vs) (LamV (Var 0))) vs))
      (e.[subst_list_val vs]).
  Proof.
    apply wrap_funs_vals_eval'.
    by rewrite replicate_length -Hl.
    apply Forall_replicate. intro σ. by asimpl.
    revert Hl. revert Γ.
    induction vs; first by constructor.
    intros Γ p. destruct Γ. inversion p. inversion p. simpl.
    constructor. apply rtc_once. apply head_prim_step.
    econstructor. by rewrite to_of_val. apply (IHvs l H0).
  Qed.

  Context (τ : type).

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Lemma wrap_funs_vals_help (Γ' : list type) :
    ∀ (HΓ' : Forall Closed Γ') (F F' : expr) vs vs' (Hl : length vs = length Γ'),
      ⊢ exprel_typed s (GammaType Γ' τ) F F' -∗ ([∗ list] v;v' ∈ vs;vs', valrel v v') -∗
        exprel_typed s τ
          (wrap_funs_vals F (zip ((λ τ : type, ep_pair Project τ) <$> Γ') vs))
          (wrap_funs_vals F' (zip (replicate (length vs') (LamV (%0)%Eₙₒ)) vs')).
  Proof.
    induction Γ' as [|τn Γ' IHΓ'] using rev_ind.
    - iIntros (_ F F' vs vs' Hl) "HF Hlist". destruct vs;[|inversion Hl].
      iDestruct (big_sepL2_length with "Hlist") as "%Hl'". destruct vs';[|inversion Hl']. simpl.
      rewrite /GammaType /=. iApply "HF".
    - iIntros (HC F F' vs vs' Hl) "HF Hlist".
      destruct (iffLR (Forall_app _ _ _) HC) as [HC1 HC2].
      destruct vs as [|v vs _] using rev_ind. { exfalso. rewrite /= app_length /= in Hl. lia. }
      iDestruct (big_sepL2_app_inv_l with "Hlist") as (ws' w') "(-> & #Hlist & Hw)".
      iDestruct (big_sepL2_length with "Hw") as "%Hl''".
      destruct w' as [|w' rem _] using rev_ind. { exfalso. rewrite /= in Hl''. lia. }
      destruct rem as [|r rem _] using rev_ind; [|exfalso; rewrite /= !app_length /= in Hl''; lia ]. clear Hl''.
      iDestruct (big_sepL2_length with "Hlist") as "%Hl'". rewrite !app_length /= in Hl.
      rename w' into v', ws' into vs'. rewrite app_nil_l. iDestruct "Hw" as "[#Hw _]".
      (* okay; eliminating one *)
      rewrite !fmap_app /= app_length /= replicate_plus !zip_snoc; (try rewrite fmap_length; try lia); (try by rewrite replicate_length).
      rewrite !wrap_funs_vals_snoc.
      rewrite !wrap_funs_vals_rw !fill_AppGamma_ectx.
      iApply (lift_bind with "[HF Hw]").
      iApply (lift_bind _ [AppLCtx _] [AppLCtx _] with "HF").
      iIntros (f f') "#Hff". simpl.
      iApply (lift_bind _ [AppRCtx _] [AppRCtx _]).
      iApply (lift_step). auto_STLCmuVS_step. simplify_custom.
      iApply project_connective; auto. by inversion HC2.
      iIntros (w w') "Hww".
      simpl. rewrite -GammaType_snoc valrel_typed_TArrow_unfold. by iApply "Hff".
      setoid_rewrite <- fill_AppGamma_ectx.
      setoid_rewrite <- wrap_funs_vals_rw.
      (* using induction *)
      iIntros (f f') "#Hff".
      iApply (IHΓ' HC1 (of_val f) (of_val f') vs vs' ltac:(lia)); auto.
      by iApply lift_val.
  Qed.

  Context (C : ctx) (n : nat) (pn : length Γ = S n) (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).
  Context (pΓ : Forall Closed Γ) (pτ : Closed τ).

  Lemma rel_back_ctx_cons :
    ctx_rel_typed MaybeStuck (back_ctx_cons C Γ τ) C Γ τ [] TUnit.
  Proof.
    assert (H : |sC> 0 ⊢ₙₒ universe_back_ctx C ☾ length Γ ☽).
    { change 0 with (length ([] : list type)).
      replace (length Γ) with (length (replicate (length Γ) TUniverse)).
      eapply (ctx_typed_scoped (replicate (length Γ) TUniverse) TUniverse []).
      change [] with (replicate 0 TUniverse).
        by apply universe_back_ctx_typed. by rewrite replicate_length. }
    (* step *)
    iIntros (e e' pe pe' Hee'). apply open_exprel_typed_nil.
    iApply lift_step_later. simpl. rewrite -> pn at 1. rewrite fill_LamGamma_ctx. rewrite -LamGammaV_S_rw. auto_STLCmuVS_step. iEval simplify_custom. change (Lam ?e) with (of_val (LamV e)). rewrite LamGammaV_S_rw -pn. rewrite ep_pair_Closed; [|by intro σ; asimpl]. iNext.
    (* connective lemma *)
    iApply (project_connective_expr TUnit). by intro σ; asimpl.
    (* rewriting substitutions *)
    rewrite !subst_fill_ctx. erewrite !(subst_closed_ctx _ _ (length Γ)); eauto. erewrite !(subst_closed_ctx_cont _ _ (length Γ)); eauto. simpl.
    rewrite ep_pair_Closed; auto.
    (* using relatedness C to translation in universe *)
    iApply open_exprel_nil'.
    apply (universe_back_ctx_in_relation _ _ C pCscp); auto.
    (* introducing stuff *)
    iIntros (vs vs' Hl) "#Hvs". simpl. rewrite ep_pair_Closed; auto.
    (* collecting info *)
    iDestruct (big_sepL2_length with "Hvs") as "%Hl'".
    (* connective lemma *)
    iApply (embed_connective_expr τ); auto.
    (* rewriting substitutions *)
    rewrite !wrap_funs_vars_subst1'. asimpl.
    rewrite !(iter_up (length Γ) (length Γ)). destruct (lt_dec (length Γ) (length Γ)); first by lia. asimpl. rewrite Nat.sub_diag. asimpl.
    assert (Hc : Closed (LamGamma (length Γ) e)).
    { rewrite -fill_LamGamma_ctx. apply expr_Closed_n.
      eapply scoped_ctx_fill; eauto.
      change 0 with (length ([] : list type)).
      eapply ctx_typed_scoped.
      apply (LamGamma_ctx_typed _ τ).
    } rewrite Hc.
    rewrite !wrap_funs_vars_subst2'; auto. assert (Hl'' : length vs' = length Γ) by by rewrite -Hl' Hl.
    iApply (lift_anti_steps_spec _ _ _ _ _ (subst_list_val_anti_steps e' vs' Hl'')).
    iApply wrap_funs_vals_help; eauto.
    rewrite -!fill_LamGamma_ctx.
    iApply open_exprel_typed_nil'.
    eapply (auto_related_ctx_typed _ _ _ _ _ (LamGamma_ctx (length Γ))).
    apply (LamGamma_ctx_typed _ τ).
    (* remaining goals *)
    all: auto; try rewrite fmap_length; try lia.
    all: eapply Forall_fmap, Forall_impl; eauto; intros; simpl; by apply ep_pair_Closed.
  Qed.

End syn_le_un_S_n.

Section syn_le_un.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (Γ : list type) (pΓ : Forall Closed Γ) (τ : type) (pτ : Closed τ).

  Context (C : ctx) (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).

  Lemma rel_back_ctx :
    ctx_rel_typed MaybeStuck (back_ctx C Γ τ) C Γ τ [] TUnit.
  Proof.
    destruct (length Γ) eqn:eq.
    - destruct Γ; [|by inversion eq]. by apply rel_back_ctx_nil.
    - rewrite /back_ctx. rewrite eq. eapply rel_back_ctx_cons; eauto.
      by rewrite eq.
  Qed.

End syn_le_un.
