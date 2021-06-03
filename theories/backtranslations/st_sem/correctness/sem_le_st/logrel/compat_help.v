From iris Require Import program_logic.weakestpre.
From iris.program_logic Require Import ectx_language ectxi_language.
From st.lamst Require Import lang types typing.
From st.backtranslations.st_sem.correctness.sem_le_st.logrel Require Import lift definition.

Lemma rtc_bind_help n e w u σ σ' u' σ'' :
  nsteps lamst_step n (σ, RunST e) (σ'', of_val u') →
  rtc lamst_step (σ'', RunST (App (of_val w) (of_val u'))) (σ', of_val u) →
  rtc lamst_step (σ, RunST (Bind e (of_val w))) (σ', of_val u).
Proof.
   revert w e u u' σ σ' σ''.
    induction n => w e u u' σ σ' σ'' Hrd1 Hrd2 /=.
  - inversion Hrd1 as [Hs1 Hs2 Hs3 Hs4|]; subst.
    assert (Hkv : to_val (RunST e) = Some u') by
        by rewrite H to_of_val.
    exfalso; by inversion Hkv.
  - inversion Hrd1 as [|Hs1 Hs2 [σ2 e2] Hs4 Hs5 Hs6]; subst; simpl in *.
    inversion Hs5 as [? ? ? Hfl ? Hhd]; subst.
    destruct K as [|[] K] using rev_ind; simpl in *;
      (try rewrite fill_app /= in Hfl); inversion Hfl; subst.
    + inversion Hhd; subst.
      * specialize (IHn _ _ _ _ _ _ _ Hs6 Hrd2).
        apply rtc_l with (y := (σ2, RunST (Bind e' w))); eauto.
        apply head_prim_step.
        econstructor.
        inversion H1 as [K ? ? ?]; subst.
        eapply (@Ectx_step eff_ectx_lang _ _ _ _ _ _ (K ++ [BindECtx _])); eauto;
          by rewrite /= (@fill_app eff_ectxi_lang) /=.
      * inversion Hs6; subst; simpl in *.
        -- eapply rtc_l; simpl; eauto.
           apply head_prim_step.
           econstructor.
           apply head_prim_step.
           econstructor; eauto using to_of_val.
        -- destruct y. erewrite (language.val_stuck) in H1; eauto. inversion H1.
    + rewrite fill_app in Hs6 Hrd2. specialize (IHn _ _ _ _ _ _ _ Hs6 Hrd2).
      apply rtc_l with (y := (σ2, (RunST (Bind (fill K e2') (of_val w))))); auto.
      apply (fill_prim_step [BindLCtx _; RunSTCtx]).
      apply (fill_prim_step K). by apply head_prim_step.
Qed.

Lemma rtc_bind_lemma (σ0 σ1 σ2 σ3 : state) (v f w s r : val) :
  rtc lamst_step (σ0, RunST v) (σ1, of_val w) →
  rtc lamst_step (σ1, ((of_val f) (of_val w))) (σ2, of_val s) →
  rtc lamst_step (σ2, RunST s) (σ3, of_val r) →
  rtc lamst_step (σ0, RunST (Bind v f)) (σ3, of_val r).
Proof.
  intros H0 H1 H2. destruct (rtc_nsteps _ _ H0) as [n H0'].
  apply (rtc_bind_help _ _ _ _ _ _ _ _ H0').
  apply rtc_transitive with (y := (σ2, RunST s)). by apply (fill_lamst_step_rtc [RunSTCtx]).
  auto.
Qed.

From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.
From st.backtranslations.st_sem Require Import ghost heap_emul.base.
From st.lam Require Import lang.

Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section valrel_cons_ren.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Context `{genHeapG_inst : !gen_heapG loc lamst.lang.val Σ}.

  Context `{val_ghost_mapG_inst : !ghost_mapG Σ nat val}.
  Context `{loc_ghost_mapG_inst : !ghost_mapG Σ nat loc}.

  (* super boring lemma *)
  Lemma valrel_typed_cons_ren γ γ' Δ : ∀ τ v v', valrel_typed ((γ,γ') :: Δ) τ.[ren (+1)] v v' ⊣⊢ valrel_typed Δ τ v v'.
  Proof.
    iLöb as "IHlob".
    iIntros (τ). iInduction τ as [ | | | τ1 τ2 | τ1 τ2 | τ1 τ2 | τb | | τ1 τ2 | τ1 τ2 ] "IH".
    - setoid_rewrite valrel_typed_TUnit_unfold; auto.
    - setoid_rewrite valrel_typed_TBool_unfold; auto.
    - setoid_rewrite valrel_typed_TInt_unfold; auto.
    - setoid_rewrite valrel_typed_TProd_unfold.
      iIntros (v v').
      iSplit.
      + iIntros "Hdes". iDestruct "Hdes" as (v1 v2 v1' v2') "(eq1 & eq2 & H1 & H2)".
        repeat iExists _. repeat iSplit; auto. by iApply "IH". by iApply "IH1".
      + iIntros "Hdes". iDestruct "Hdes" as (v1 v2 v1' v2') "(eq1 & eq2 & H1 & H2)".
        repeat iExists _. repeat iSplit; auto. by iApply "IH". by iApply "IH1".
    - setoid_rewrite valrel_typed_TSum_unfold.
      iIntros (v v').
      iSplit.
      + iIntros "Hdes". iDestruct "Hdes" as (v1 v1') "[(eq1 & eq2 & H) | (eq1 & eq2 & H)]".
        * repeat iExists _. iLeft. repeat iSplit; eauto. by iApply "IH".
        * repeat iExists _. iRight. repeat iSplit; eauto. by iApply "IH1".
      + iIntros "Hdes". iDestruct "Hdes" as (v1 v1') "[(eq1 & eq2 & H) | (eq1 & eq2 & H)]".
        * repeat iExists _. iLeft. repeat iSplit; eauto. by iApply "IH".
        * repeat iExists _. iRight. repeat iSplit; eauto. by iApply "IH1".
    - setoid_rewrite valrel_typed_TArrow_unfold.
      iIntros (w w'). iSplit.
      + iIntros "#H". iModIntro. iIntros (v v') "#H1".
        iApply (lift_wand _ (valrel_typed ((γ,γ') :: Δ) τ3.[ren (+1)])). iIntros (x x') "Hxx'". by iApply "IH1".
        iApply "H". by iApply "IH".
      + iIntros "#H". iModIntro. iIntros (v v') "#H1".
        iApply (lift_wand _ (valrel_typed (Δ) τ3)). iIntros (x x') "Hxx'". by iApply "IH1".
        iApply "H". by iApply "IH".
    - setoid_rewrite valrel_typed_TRec_unfold.
      iIntros (v v'). iSplit.
      + iIntros "Hdes". iDestruct "Hdes" as (w w') "(eq & eq' & H)".
        iExists w, w'. repeat iSplit; auto. iNext. iApply "IHlob". by asimpl.
      + iIntros "Hdes". iDestruct "Hdes" as (w w') "(eq & eq' & H)".
        iExists w, w'. repeat iSplit; auto. iNext.
        assert (τb.[up (ren (+1))].[TRec τb.[up (ren (+1))]/] =
                τb.[TRec τb/].[ren (+1)]
               ) as eq; first by asimpl. rewrite eq. by iApply "IHlob".
    - setoid_rewrite valrel_typed_TVar_unfold. auto.
    - setoid_rewrite valrel_typed_TSTRef_unfold; auto.
      destruct τ1; auto; destruct (Δ !! X) as [[γ'' γ''']|] eqn:eq; rewrite /= eq; try done.
      iIntros (v v'). iSplit.
      + iIntros "Hdes". iDestruct "Hdes" as (i l) "(-> & -> & Hil & H)". iExists i, l. repeat iSplit; auto.
        iApply (inv_iff with "H"). repeat iModIntro. iSplit.
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi [Hl Hww']]". iExists w, w'. iFrame "Hi Hl". by iApply "IH1".
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi [Hl Hww']]". iExists w, w'. iFrame "Hi Hl". by iApply "IH1".
      + iIntros "Hdes". iDestruct "Hdes" as (i l) "(-> & -> & Hil & H)". iExists i, l. repeat iSplit; auto.
        iApply (inv_iff with "H"). repeat iModIntro. iSplit.
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi [Hl Hww']]". iExists w, w'. iFrame "Hi Hl". by iApply "IH1".
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi [Hl Hww']]". iExists w, w'. iFrame "Hi Hl". by iApply "IH1".
    - setoid_rewrite valrel_typed_TST_unfold; auto.
      destruct τ1; auto; destruct (Δ !! X) as [[γ'' γ''']|] eqn:eq; rewrite /= eq; try done.
      iIntros (w w'). iSplit.
      + iIntros "#H". iIntros (ps σ). iModIntro. iIntros "Hσ AuthVals AuthLocs". iSpecialize ("H" $! ps σ with "Hσ AuthVals AuthLocs"). iApply (wp_wand with "H").
        iIntros (v) "Hdes". iDestruct "Hdes" as (w1 w1' ps1 σ1) "(-> & Hσ1 & Hauth1 & Hauth2 & Hstep & H)". iExists w1, w1', ps1, σ1. iFrame. iSplit; auto.
        by iApply "IH1".
      + iIntros "#H". iIntros (ps σ). iModIntro. iIntros "Hσ AuthVals AuthLocs". iSpecialize ("H" $! ps σ with "Hσ AuthVals AuthLocs"). iApply (wp_wand with "H").
        iIntros (v) "Hdes". iDestruct "Hdes" as (w1 w1' ps1 σ1) "(-> & Hσ1 & Hauth1 & Hauth2 & Hstep & H)". iExists w1, w1', ps1, σ1. iFrame. iSplit; auto.
        by iApply "IH1".
  Qed.

End valrel_cons_ren.
