From iris.program_logic Require Import weakestpre lifting ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.

Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

From st.prelude Require Import big_op_three.

From st.lam Require Import lang.
From st.lamst Require Import wkpre lang types typing.

From st.backtranslations.st_sem Require Import help expressions ghost heap_emul.base heap_emul.spec.
From st.backtranslations.st_sem.correctness.st_le_sem.logrel Require Import lift definition.
From st Require Import resources.

Section prim_step_lemmas.

  Lemma inv_prim_step_RunST_Alloc_val (e1 e2 : expr) (v : val) (σ1 σ2 : state) κ efs (Hstep : prim_step (RunST (Alloc v)) σ1 κ e2 σ2 efs) :
    ∃ l : loc, σ1 !! l = None ∧ κ = [] ∧ efs = [] ∧ e2 = (RunST (Return l)) ∧ σ2 = <[ l := v ]> σ1.
  Proof.
    simpl in *.
    assert (efs = []) as ->. by eapply ST_step_no_spawn.
    assert (κ = []) as ->. by eapply ST_step_no_obs.
    assert (Hheadstep : head_step (RunST (Alloc v)) σ1 [] e2 σ2 []). apply (@head_reducible_prim_step lamst_ectx_lang); auto.
    { exists [], (RunST $ Return $ Lit $ LitLoc $ fresh_loc σ1), (<[fresh_loc σ1:=v]> σ1), []. simpl.
      apply RunST_eff_head_step, head_prim_step, Alloc_val_eff_head_step.
      by eapply fresh_loc_lookup_None.
      by rewrite to_of_val.
    }
    inversion_clear Hheadstep. simpl in *.
    assert (Heffheadstep : eff_head_step (Alloc v) σ1 [] e' σ2 []). apply (@head_reducible_prim_step eff_ectx_lang); auto.
    { exists [], (Return $ Lit $ LitLoc $ fresh_loc σ1), (<[fresh_loc σ1:=v]> σ1), []. simpl.
      apply Alloc_val_eff_head_step.
      by eapply fresh_loc_lookup_None.
      by rewrite to_of_val.
    }
    inversion_clear Heffheadstep. exists l. rewrite to_of_val in H1. inversion H1.
    simplify_eq. auto.
  Qed.

  Lemma inv_prim_step_RunST_Return_val (e2 : expr) (v : val) (σ1 σ2 : state) κ efs (Hstep : prim_step (RunST (Return v)) σ1 κ e2 σ2 efs) :
    κ = [] ∧ efs = [] ∧ e2 = (of_val v) ∧ σ1 = σ2.
  Proof.
    simpl in *.
    assert (efs = []) as ->. by eapply ST_step_no_spawn.
    assert (κ = []) as ->. by eapply ST_step_no_obs.
    assert (Hheadstep : head_step (RunST (Return v)) σ1 [] e2 σ2 []). apply (@head_reducible_prim_step lamst_ectx_lang); auto.
    { exists [], (of_val v), σ1, []. simpl. eapply RunST_Return_head_step. by rewrite to_of_val.
    }
    inversion_clear Hheadstep; auto.
    exfalso. inversion H. destruct K using rev_ind.
    - simpl in H0. rewrite -H0 in H2. inversion H2.
    - simpl in H0. rewrite fill_app in H0. destruct x; inversion H0.
  Qed.

  Lemma inv_prim_step_Compare_locs (l1 l2 : loc) e2 (σ1 σ2 : state) κ efs (Hstep : prim_step (Compare l1 l2) σ1 κ e2 σ2 efs) :
    κ = [] ∧ efs = [] ∧ e2 = (bool_decide (l1 = l2)) ∧ σ1 = σ2.
  Proof.
    simpl in *.
    assert (efs = []) as ->. by eapply ST_step_no_spawn.
    assert (κ = []) as ->. by eapply ST_step_no_obs.
    assert (Hheadstep : head_step (Compare l1 l2) σ1 [] e2 σ2 []). apply (@head_reducible_prim_step lamst_ectx_lang); auto.
    { exists [], (of_val $ bool_decide (l1 = l2)), σ1, []. simpl.
      destruct (decide (l1 = l2)) as [<- | neq].
      + rewrite bool_decide_eq_true_2; auto.
        apply Compare_suc_head_step.
      + rewrite bool_decide_eq_false_2; auto.
        by apply Compare_fail_head_step.
    }
    inversion_clear Hheadstep; auto;
      [by rewrite bool_decide_eq_true_2 | by rewrite bool_decide_eq_false_2].
  Qed.

  Lemma inv_prim_step_RunST_Read (e2 : expr) (l : loc) (σ1 σ2 : state) κ efs (Hstep : prim_step (RunST (Read l)) σ1 κ e2 σ2 efs) :
    ∃ v : val, σ1 !! l = Some v ∧ κ = [] ∧ efs = [] ∧ e2 = (RunST (Return v)) ∧ σ2 = σ1.
  Proof.
    simpl in *.
    assert (efs = []) as ->. by eapply ST_step_no_spawn.
    assert (κ = []) as ->. by eapply ST_step_no_obs.
    inversion_clear Hstep as [K e1' e2' eq1 eq2 Hheadstep]; simpl in *.
    destruct K as [|Ki K] using rev_ind; simpl in *.
    - rewrite -eq1 -eq2 in Hheadstep. clear e2' e1' eq1 eq2.
      inversion_clear Hheadstep. inversion_clear H. simplify_eq.
      destruct K as [|Ki K] using rev_ind; simpl in *; simplify_eq.
      + inversion H2. simplify_eq. by exists v.
      + exfalso. clear IHK. rewrite /= fill_app in H0. destruct Ki. inversion H0.
    - exfalso. clear IHK. rewrite !fill_app /= in eq1 eq2. destruct Ki; inversion eq1. simpl in *. simplify_eq.
      destruct K as [|Ki K] using rev_ind.
      + simpl in *. rewrite -H0 in Hheadstep. inversion Hheadstep.
      + clear IHK. rewrite !fill_app /= in eq1. destruct Ki; inversion eq1.
        destruct K as [|Ki K] using rev_ind; auto.
        * simpl in *. simplify_eq. inversion Hheadstep.
        * clear IHK. rewrite fill_app /= in H1. destruct Ki; inversion H1.
  Qed.

  Lemma inv_prim_step_RunST_Write_val e2 (v2 : val) (l : loc) (σ1 σ2 : state) κ efs (Hstep : prim_step (RunST (Write l v2)) σ1 κ e2 σ2 efs) :
    is_Some (σ1 !! l) ∧ κ = [] ∧ efs = [] ∧ e2 = (RunST (Return ()%Vₛₜ)) ∧ σ2 = <[ l := v2 ]> σ1.
  Proof.
    simpl in *.
    assert (efs = []) as ->. by eapply ST_step_no_spawn.
    assert (κ = []) as ->. by eapply ST_step_no_obs.
    inversion_clear Hstep as [K e1' e2' eq1 eq2 Hheadstep]; simpl in *.
    destruct K as [|Ki K] using rev_ind; simpl in *.
    - rewrite -eq1 -eq2 in Hheadstep. clear e2' e1' eq1 eq2.
      inversion_clear Hheadstep. inversion_clear H. simplify_eq.
      destruct K as [|Ki K] using rev_ind; simpl in *; simplify_eq.
      + inversion H2. simplify_eq. rewrite to_of_val in H4. inversion_clear H4. auto.
      + exfalso. clear IHK. rewrite /= fill_app in H0. destruct Ki. inversion H0.
    - exfalso. clear IHK. rewrite !fill_app /= in eq1 eq2. destruct Ki; inversion eq1. simpl in *. simplify_eq. clear H0.
      destruct K as [|Ki K] using rev_ind.
      + simpl in *. rewrite -eq1 in Hheadstep. inversion Hheadstep.
      + clear IHK. rewrite !fill_app /= in eq1. destruct Ki; inversion eq1.
        * simpl in *. simplify_eq. destruct K as [|Ki K] using rev_ind; auto.
          -- simpl in *. simplify_eq. inversion Hheadstep.
          -- clear H0. clear IHK. rewrite !fill_app /= in eq1. destruct Ki; inversion eq1.
        * simpl in *. simplify_eq. clear H0 H1.
          destruct (@fill_val e1' K) as [v1' eq]. rewrite -H. rewrite to_of_val. by eexists.
          assert (to_val e1' = None). erewrite val_head_stuck; eauto. simplify_eq.
  Qed.

  Lemma inv_prim_step_RunST_Bind_vals (v1 v2 : val) (e' : expr) (σ σ' : state)
        (Hstep : prim_step (RunST (Bind v1 v2)) σ [] e' σ' []) :
    (∃ (v : val), of_val v1 = Return v ∧ e' = RunST (v2 v) ∧ prim_step (RunST (Return v)) σ [] v σ' []) ∨
    (∃ e1', e' = RunST (Bind e1' v2) ∧ prim_step (RunST v1) σ [] (RunST e1') σ' []).
  Proof.
    inversion Hstep as [K e e'' eq eq' Hheadstep]. simpl in *. rewrite eq'.
    destruct K as [|Ki K] using rev_ind; simpl in *.
    (* destruct K as [|Ki K]; simpl in *. *)
    - simplify_eq. inversion_clear Hheadstep. inversion_clear H. simpl in *.
      destruct K as [|Ki K] using rev_ind.
      (* simpl in *; simplify_eq. *)
      + simpl in *. simplify_eq.
        inversion H2. simplify_eq. left. exists v0. rewrite (of_to_val _ _ H1). repeat split; auto.
        destruct v1; inversion H. apply head_prim_step. econstructor. by rewrite to_of_val.
      + clear IHK. rewrite !fill_app in H0, H1. destruct Ki. simpl in *. inversion H0. simplify_eq.
        right. exists (@fill eff_ectxi_lang K e2'). split; auto. apply head_prim_step. constructor. rewrite H0.
        by eapply Ectx_step with (K0 := K).
    - exfalso. clear IHK. rewrite !fill_app /= in eq, eq'. destruct Ki; inversion eq. simpl in *.
      destruct K as [|Ki K] using rev_ind.
      + simpl in *. simplify_eq. inversion Hheadstep.
      + clear IHK. rewrite !fill_app /= in eq' H0 eq. simplify_eq. clear H0.
        destruct Ki; inversion eq.
        * simpl in *. destruct (@fill_val e K) as [v' eq']. exists v1. rewrite -H0. by rewrite to_of_val.
          rewrite (val_head_stuck e _ _ _ _ _ Hheadstep) in eq'. inversion eq'.
        * simpl in *. simplify_eq.
          destruct (@fill_val e K) as [v' eq']. exists v2. rewrite -eq. by rewrite to_of_val.
          rewrite (val_head_stuck e _ _ _ _ _ Hheadstep) in eq'. inversion eq'.
  Qed.

  Lemma pure_step_RunST_Return_val (v : val) : pure_step (RunST (Return v)) (of_val v).
  Proof.
    split.
    - intros σ. rewrite /reducible_no_obs. exists (of_val v), σ, [].
      apply head_prim_step. econstructor. by rewrite to_of_val.
    - intros. simpl in H. by destruct (inv_prim_step_RunST_Return_val _ _ _ _ _ _ H) as (-> & -> & -> & ->).
  Qed.

  Lemma pure_step_eq_loc (l1 l2 : loc) : pure_step (Compare l1 l2)%Eₛₜ (of_val $ bool_decide (l1 = l2)).
  Proof.
    split.
    - intros σ. rewrite /reducible_no_obs.
      exists (of_val $ bool_decide (l1 = l2)), σ, [].
      destruct (decide (l1 = l2)) as [<- | neq].
      + rewrite bool_decide_eq_true_2; auto. apply head_prim_step.
        (* Unset Printing Notations. Set Printing Coercions. *)
        apply Compare_suc_head_step.
      + rewrite bool_decide_eq_false_2; auto. apply head_prim_step.
        by apply Compare_fail_head_step.
    - intros. simpl in H.
      by destruct (inv_prim_step_Compare_locs _ _ _ _ _ _ _ H) as (-> & -> & -> & ->).
  Qed.

End prim_step_lemmas.

Section compat_help.

  Context `{Σ : !gFunctors} `{st_le_semΣ_inst : !st_le_semΣ Σ}.

  Lemma wp_alloc {s : stuckness} (v : val) : ⊢ WP RunST (Alloc v) @ s; ⊤ {{ w, ∃ (l : loc), ⌜ w = l ⌝ ∧ l ↦ v }}.
  Proof.
    iApply wp_lift_step. auto.
    iIntros (σ1 n κ κ' m) "Hσ1". simpl.
    iApply fupd_frame_l. iSplitL "". iPureIntro.
    { destruct s; auto. exists [], (RunST $ Return $ Lit $ LitLoc $ fresh_loc σ1), (<[fresh_loc σ1:=v]> σ1), [].
      apply head_prim_step, RunST_eff_head_step.
      apply head_prim_step, Alloc_val_eff_head_step.
      by eapply fresh_loc_lookup_None.
      by rewrite to_of_val.
    }
    iApply fupd_mask_intro. auto. iIntros "Hclose".
    iNext. (* !!!! *)
    iIntros (e2 σ2 efs) "%Hstep".
    destruct (inv_prim_step_RunST_Alloc_val (RunST (Alloc v)) _ _ _ _ _ _ Hstep) as (l & eq & -> & -> & -> & ->).
    iMod ((gen_heap_alloc σ1 l v eq) with "Hσ1") as "[Hσ2 [Hl blaa]]".
    iApply fupd_wand_r. iFrame "Hclose". iIntros (_). iFrame "Hσ2". simpl. iSplitL; auto.
    (* !!! *)
    iApply wp_pure_step_later.
    { split.
      - intro σ. exists (Lit l), σ, []. apply head_prim_step. econstructor. by simpl.
      - intros. change (Lit l) with (of_val $ LitV l) in H.
        simpl in H. destruct (inv_prim_step_RunST_Return_val e2' l _ _ _ _ H) as (-> & -> & -> & ->).
        auto.
    }
    (* !!! *)
    iNext. change (Lit l) with (of_val l). iApply wp_value'. iExists l. auto.
  Qed.

  Lemma wp_runst_bind Φ : ∀ (e1 : expr) (v2 : val), WP RunST e1 ?{{ w, WP RunST (v2 w) ?{{Φ}}}} ⊢ WP RunST (Bind e1 v2) ?{{Φ}}.
  Proof.
    iLöb as "IHlob".
    iIntros (e1 v2) "H".
    iApply (wp_bind (fill [BindLCtx _; RunSTCtx])).
    iApply (wp_wand with "[H]"). iApply (wp_bind_inv (fill [RunSTCtx])). iApply "H". simpl.
    iIntros (v1) "H".
    (* okay *)
    rewrite !wp_unfold /wp_pre /=.
    iIntros (σ n κ κ' m) "Hσ". iSpecialize ("H" $! σ n κ κ' m with "Hσ"). simpl.
    iApply fupd_wand_l. iFrame "H". iIntros "[_ H]". iSplitL ""; auto.
    iIntros (e σ2 efs) "%Hstep". assert (efs = []) as ->. by eapply ST_step_no_spawn. assert (κ = []) as ->. by eapply ST_step_no_obs.
    destruct (inv_prim_step_RunST_Bind_vals _ _ _ _ _ Hstep) as [(v & -> & -> & Hstep') | (e1' & -> & Hstep')].
    - iSpecialize ("H" $! (of_val v) σ2 [] Hstep'). iMod "H"; iModIntro. iModIntro. iMod "H"; iModIntro.
      iApply fupd_wand_r. iSplitL "H". auto.
      iIntros "[H1 [H2 H3]]". iFrame "H1 H3". by iApply (wp_bind (fill [AppRCtx _; RunSTCtx])).
    - iSpecialize ("H" $! (RunST e1') σ2 [] Hstep'). iMod "H"; iModIntro. iModIntro. iMod "H"; iModIntro.
      iApply fupd_wand_r. iSplitL "H". auto.
      iIntros "[H1 [H2 H3]]". iFrame "H1 H3". by iApply "IHlob".
  Qed.

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
      + iIntros "Hdes". iDestruct "Hdes" as (i l) "(-> & Hil & -> & H)". iExists i, l. repeat iSplit; auto.
        iApply (inv_iff with "H"). repeat iModIntro. iSplit.
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi [Hl Hww']]". iExists w, w'. iFrame "Hi Hl". by iApply "IH1".
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi [Hl Hww']]". iExists w, w'. iFrame "Hi Hl". by iApply "IH1".
      + iIntros "Hdes". iDestruct "Hdes" as (i l) "(-> & Hil & -> & H)". iExists i, l. repeat iSplit; auto.
        iApply (inv_iff with "H"). repeat iModIntro. iSplit.
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi [Hl Hww']]". iExists w, w'. iFrame "Hi Hl". by iApply "IH1".
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi [Hl Hww']]". iExists w, w'. iFrame "Hi Hl". by iApply "IH1".
    - setoid_rewrite valrel_typed_TST_unfold; auto.
      destruct τ1; auto; destruct (Δ !! X) as [[γ'' γ''']|] eqn:eq; rewrite /= eq; try done.
      iIntros (w w'). iSplit.
      + iIntros "#H". iIntros (ps). iModIntro. iIntros "Hauth". iSpecialize ("H" $! ps with "Hauth"). iApply (wp_wand with "H").
        iIntros (v) "Hdes". iDestruct "Hdes" as (w1 ps1) "(Hauth1 & Hauth2 & Hstep & H)". iExists w1, ps1. iFrame "Hauth1 Hauth2 Hstep".
        by iApply "IH1".
      + iIntros "#H". iIntros (ps). iModIntro. iIntros "Hauth". iSpecialize ("H" $! ps with "Hauth"). iApply (wp_wand with "H").
        iIntros (v) "Hdes". iDestruct "Hdes" as (w1 ps1) "(Hauth1 & Hauth2 & Hstep & H)". iExists w1, ps1. iFrame "Hauth1 Hauth2 Hstep".
        by iApply "IH1".
  Qed.

End compat_help.
