From iris Require Import program_logic.weakestpre.
From iris Require Import base_logic.lib.invariants.
From st.STLCmuST Require Import lang types typing.
From st.STLCmuVS Require Import lang wkpre generic.lift tactics.
From st.backtranslations.st_sem.well_defined.logrel Require Import definition.
From iris.proofmode Require Import tactics.
From st.backtranslations.st_sem Require Import ghost heap_emul.base heap_emul.spec expressions.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import big_op_three.
From st Require Import resources.

Section compat_lemmas.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Opaque alloc.

  Lemma compat_alloc Γ e e' ρ τ (Hee' : open_exprel_typed Γ e e' τ) :
    open_exprel_typed Γ (alloc e) (alloc e') (TST ρ (TSTref ρ τ)).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    rewrite /= !alloc_Closed.
    iApply (lift_bind' _ _ _ [AppRCtx _] [AppRCtx _] with "Hee'").
    simpl. iIntros (v v') "#Hvv'". iClear "Hee'".
    (* steps *)
    iApply lift_step_later. apply alloc_step.
    iApply lift_step. apply alloc_step.
    iNext.
    (* *)
    iApply lift_val.
    rewrite valrel_typed_TST_unfold.
    destruct ρ; auto. destruct (Δ !! X) as [γ|]eqn:eq; auto.
    (*  *)
    iIntros (psᵢ). iModIntro. iIntros "Hγvs".
    iApply wp_rtc_steps. apply alloc_v_steps.
    change ((encode (psᵢ.*1 ++ [v]), length psᵢ.*1)%Eₙₒ) with (of_val (encode (psᵢ.*1 ++ [v]), length psᵢ.*1)%Vₙₒ). iApply wp_value_fupd'.
    iExists (length psᵢ.*1), (length psᵢ.*2), (psᵢ ++ [(v, v')]).
    iDestruct ((ghost_alloc _ _ (v, v')) with "Hγvs") as "H".
    iApply fupd_trans.
    iMod "H". iModIntro.
    iDestruct "H" as "[H1 H2]". iFrame "H1".
    iSplitR. by rewrite fmap_app /=.
    iSplitR. iModIntro. iPureIntro. rewrite fmap_app /=. apply alloc_v_steps.
    rewrite valrel_typed_TSTRef_unfold. rewrite eq.
    iExists (length psᵢ).
    iSplitR. iPureIntro. by rewrite map_length.
    iSplitR. iPureIntro. by rewrite map_length.
    iApply inv_alloc. iNext. iExists v, v'. auto.
  Qed.

  Opaque read.

  Instance val_inhabited : Inhabited val := populate ()%Vₙₒ.

  Lemma compat_read Γ e e' ρ τ :
    open_exprel_typed Γ e e' (TSTref ρ τ) →
    open_exprel_typed Γ (read e) (read e') (TST ρ τ).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Hee' Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    rewrite /= !read_Closed.
    iApply (lift_bind' _ _ _ [AppRCtx _] [AppRCtx _] with "Hee'").
    simpl. iIntros (v v') "#Hvv'". iClear "Hee'".
    rewrite valrel_typed_TSTRef_unfold. destruct ρ; auto. destruct (Δ !! X) as [γ|] eqn:eq; auto.
    iDestruct "Hvv'" as (i) "(-> & -> & #HInv)".
    (* steps *)
    iApply lift_step_later. apply read_step.
    iApply lift_step. apply read_step.
    iApply lift_val.
    (* proving relatedness... *)
    rewrite valrel_typed_TST_unfold. rewrite eq.
    iIntros (psᵢ).
    do 2 iModIntro. iIntros "Hγ".
    iApply fupd_wp. iInv "HInv" as "HContents" "HClose".
    iEval (rewrite bi.later_exist) in "HContents". iDestruct "HContents" as (w) "HContents".
    iEval (rewrite bi.later_exist) in "HContents". iDestruct "HContents" as (w') "HContents".
    iAssert (▷ (⌜ psᵢ.*1 !! i = Some w ⌝ ∗ ⌜ psᵢ.*2 !! i = Some w' ⌝ ∗ i ↪[γ] (w, w') ∗ valrel_typed Δ τ w w' ∗ auth_list γ psᵢ))%I with "[HContents Hγ]" as "H".
    iNext. iDestruct "HContents" as "[Hiγ #Hww']".
    iDestruct (ghost_read with "Hγ Hiγ") as %eq'. iFrame "Hiγ Hγ Hww'". rewrite !list_lookup_fmap eq'. auto.
    iEval (repeat rewrite bi.later_sep) in "H". iDestruct "H" as "(Hieq1 & Hieq2 & Hiγ & #Hww' & Hγ)".
    (* iEval (rewrite bi.later_sep) in "H". iDestruct "H" as "[Hieq H]". *)
    iApply fupd_wand_r. iSplitL "HClose Hiγ". iApply "HClose". iNext. iExists w, w'. iFrame "Hiγ Hww'".
    iIntros (_).
    iApply wp_read_i. iNext. iFrame "Hieq1".
    iExists w, w', psᵢ. iFrame "Hγ Hww'". iSplit; auto. iDestruct "Hieq2" as %H. iPureIntro. apply at_least_one.at_least_one_rtc. by apply read_i_at_least_one.
  Qed.

  Lemma compat_write Γ e1 e1' e2 e2' ρ τ :
    open_exprel_typed Γ e1 e1' (TSTref ρ τ) →
    open_exprel_typed Γ e2 e2' τ →
    open_exprel_typed Γ (write e1 e2) (write e1' e2') (TST ρ TUnit).
  Proof.
    Local Opaque write write_i write_i_v.
    (* cleaning and getting to the gist of it *)
    iIntros (H1 H2 Δ vs vs') "#Hvsvs'".
    specialize (H1 Δ vs vs'). specialize (H2 Δ vs vs').
    iDestruct (H1 with "Hvsvs'") as "H1". clear H1. iDestruct (H2 with "Hvsvs'") as "H2". clear H2.
    iClear "Hvsvs'".
    change ((write ?e1 ?e2).[?σ]) with (write e1.[σ] e2.[σ]).
    iApply (lift_bind' _ _ _ [AppRCtx _; AppLCtx _] [AppRCtx _; AppLCtx _] with "H1"). simpl.
    iIntros (v1 v1') "#Hv1v1'". iClear "H1".
    iApply lift_step. apply (@STLCmuVS_step_ctx (fill_item (AppLCtx _)) (ectxi_lang_ctx_item _)). apply write_step. simpl.
    iApply lift_step_later. apply (@STLCmuVS_step_ctx (fill_item (AppLCtx _)) (ectxi_lang_ctx_item _)). apply write_step. simpl.
    iApply (lift_bind' _ _ _ [AppRCtx _] [AppRCtx _] with "H2"). iNext.
    iIntros (v2 v2') "#Hv2v2'". simpl.
    iApply lift_step. apply write_i_step.
    iApply lift_step_later. apply write_i_step.
    iApply lift_val.
    (* okay *)
    rewrite valrel_typed_TSTRef_unfold; destruct ρ; auto; destruct (Δ !! X) as [γ|] eqn:eq; auto.
    iDestruct "Hv1v1'" as (i) "(-> & -> & Hinv)".
    rewrite valrel_typed_TST_unfold eq. iIntros (psᵢ). iNext. iModIntro. iIntros "Hauth".
    (* k *)
    iApply lifting.wp_pure_step_fupd. apply step_PureExec. apply write_i_v_step. auto.
    iInv "Hinv" as "HContents" "HClose". iModIntro. iNext. iDestruct "HContents" as (w w') "[Hi Hww']".
    iDestruct (ghost_read with "Hauth Hi") as %eq'.
    iDestruct ((ghost_write _ _ _ _ (v2, v2')) with "Hauth Hi") as ">[Hauth Hi]".
    iDestruct (ghost_read with "Hauth Hi") as %eq''.
    iApply fupd_wand_r. iSplitL "HClose Hi". iApply "HClose". iNext. iExists v2, v2'. auto.
    iIntros (_). iApply wp_rtc_steps. eapply write_i_v_vs_steps. by rewrite list_lookup_fmap eq'.
    iApply wp_value'.
    iExists _, _, _. iFrame "Hauth".
    rewrite !list_fmap_insert /=.
    iSplit; auto.
    iSplit. iPureIntro. eapply write_i_v_steps. by rewrite list_lookup_fmap eq'.
    rewrite valrel_typed_TUnit_unfold. auto.
  Qed.

  Lemma encode_empty_subst σ : (of_val $ encode []).[σ] = of_val (encode []).
  Proof. by asimpl. Qed.

  Lemma compat_bind Γ e1 e1' e2 e2' ρ τ1 τ2 :
    open_exprel_typed Γ e1 e1' (TST ρ τ1) →
    open_exprel_typed Γ e2 e2' (τ1 ⟶ TST ρ τ2)%Tₛₜ →
    open_exprel_typed Γ (bind e1 e2) (bind e1' e2') (TST ρ τ2).
  Proof.
    Local Opaque bind bind_v.
    (* cleaning and getting to the gist of it *)
    iIntros (H1 H2 Δ vs vs') "#Hvsvs'".
    specialize (H1 Δ vs vs'). specialize (H2 Δ vs vs').
    iDestruct (H1 with "Hvsvs'") as "H1". clear H1. iDestruct (H2 with "Hvsvs'") as "H2". clear H2.
    iClear "Hvsvs'".
    change ((bind ?e1 ?e2).[?σ]) with (bind e1.[σ] e2.[σ]).
    iApply (lift_bind' _ _ _ [AppRCtx _; AppLCtx _] [AppRCtx _; AppLCtx _] with "H1"). simpl.
    iIntros (v1 v1') "#Hv1v1'". iClear "H1".
    iApply lift_step. apply (@STLCmuVS_step_ctx (fill_item (AppLCtx _)) (ectxi_lang_ctx_item _)). apply bind_step. simpl.
    iApply lift_step_later. apply (@STLCmuVS_step_ctx (fill_item (AppLCtx _)) (ectxi_lang_ctx_item _)). apply bind_step. simpl.
    iApply (lift_bind' _ _ _ [AppRCtx _] [AppRCtx _] with "H2"). iNext.
    iIntros (v2 v2') "#Hv2v2'". simpl.
    iApply lift_step. apply bind_v_step.
    iApply lift_step_later. apply bind_v_step.
    iApply lift_val.
    (* okay *)
    rewrite /bind_v_f.
    iEval (rewrite valrel_typed_TST_unfold). destruct ρ; auto. destruct (Δ !! X) as [γ|] eqn:eq; auto.
    iNext. iIntros (ps0). iModIntro. iIntros "Hauth0".
    iApply wp_step_later. 
    apply head_prim_step. eapply App_Lam_head_step'. asimpl. change ((encode_help (reverse ps0.*1), length ps0.*1)%Eₙₒ) with (of_val $ (encode ps0.*1)%Vₙₒ) . auto. by rewrite to_of_val. iNext.
    iApply (@wp_bind _ _ _ (fill_item $ LetInCtx _) (ectxi_lang_ctx_item _)).
    iEval (rewrite valrel_typed_TST_unfold eq) in "Hv1v1'". iSpecialize ("Hv1v1'" $! ps0). iDestruct ("Hv1v1'") as "#Hv1v1'". iSpecialize ("Hv1v1'" with "Hauth0").
    iApply (wp_wand with "Hv1v1'"). iIntros (a) "H". iDestruct "H" as (r1 r1' ps1) "(Hauth1 & -> & %Hsteps & #Hr1r1')".
    Local Opaque encode.
    iEval simpl.
    iApply wp_step_later.
    apply head_prim_step. change ((encode ps1.*1, r1)%Eₙₒ) with (of_val (encode ps1.*1, r1)%Vₙₒ). eapply LetIn_head_step. by rewrite to_of_val. iNext. asimpl.
    iApply wp_step_later. apply (@STLCmuVS_step_ctx (fill_item $ LetInCtx _) (ectxi_lang_ctx_item _)). apply head_prim_step. auto_head_step. simpl.
    iApply wp_step_later. apply head_prim_step. auto_head_step. asimpl.
    iApply wp_step_later. apply (@STLCmuVS_step_ctx (fill_item $ LetInCtx _) (ectxi_lang_ctx_item _)). apply head_prim_step. auto_head_step. simpl.
    iApply wp_step_later. apply head_prim_step. auto_head_step. asimpl.
    repeat iNext.
    iEval (rewrite valrel_typed_TArrow_unfold) in "Hv2v2'".
    iSpecialize ("Hv2v2'" $! r1 r1' with "Hr1r1'").
    iApply (@wp_bind _ _ _ (fill_item $ AppLCtx _) (ectxi_lang_ctx_item _)).
    iApply (wp_wand with "Hv2v2'"). iIntros (s) "H". iDestruct "H" as (s') "(%Hsteps' & #Hss')". simpl.
    iEval (rewrite valrel_typed_TST_unfold eq) in "Hss'". iSpecialize ("Hss'" $! ps1 with "Hauth1").
    iApply (wp_wand with "Hss'"). iIntros (a) "H". iDestruct "H" as (p p' ps2) "(Hauth2 & -> & %Hsteps'' & #Hpp')".
    iExists p, p', ps2. iFrame "Hauth2 Hpp'". iSplit; auto. iPureIntro.
    eapply rtc_l. apply head_prim_step. auto_head_step. asimpl.
    eapply rtc_transitive.
    by apply (@rtc_STLCmuVS_step_ctx (fill_item $ LetInCtx _) (ectxi_lang_ctx_item _)). simpl.
    change (Pair (of_val ?v1) (of_val ?v2)) with (of_val (PairV v1 v2)).
    eapply rtc_l. apply head_prim_step. auto_head_step. asimpl.
    eapply rtc_l. apply (@STLCmuVS_step_ctx (fill_item $ LetInCtx _) (ectxi_lang_ctx_item _)). apply head_prim_step. auto_head_step. asimpl.
    eapply rtc_l. apply head_prim_step. auto_head_step. asimpl.
    eapply rtc_l. apply (@STLCmuVS_step_ctx (fill_item $ LetInCtx _) (ectxi_lang_ctx_item _)). apply head_prim_step. auto_head_step. asimpl.
    eapply rtc_l. apply head_prim_step. auto_head_step. asimpl.
    eapply rtc_transitive.
    by apply (@rtc_STLCmuVS_step_ctx (fill_item $ AppLCtx _) (ectxi_lang_ctx_item _)). by simpl.
  Qed.

  Lemma compat_retrn Γ e e' ρ τ :
    open_exprel_typed Γ e e' τ →
    open_exprel_typed Γ (retrn e) (retrn e') (TST ρ τ).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Hee' Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    change (retrn ?e).[?σ] with (retrn e.[σ]).
    iApply (lift_bind' _ _ _ [AppRCtx _] [AppRCtx _] with "Hee'").
    simpl. iIntros (v v') "#Hvv'". iClear "Hee'".
    iApply lift_step. apply head_prim_step. auto_head_step. asimpl.
    iApply lift_step_later. apply head_prim_step. auto_head_step. asimpl.
    change (Lam ?e) with (of_val $ LamV e). iApply lift_val.
    (* ok *)
    rewrite valrel_typed_TST_unfold. destruct ρ; auto. destruct (Δ !! X) as [γ|] eqn:eq; auto.
    iNext.
    iIntros (ps). iModIntro. iIntros "Hauth". iApply wp_step_later. apply head_prim_step. auto_head_step. asimpl.
    change (Pair (of_val ?v1) (of_val ?v2)) with (of_val $ (PairV v1 v2)). iApply wp_value'. iNext.
    iExists _, _, _. iFrame "Hauth Hvv'". iSplit; auto. iPureIntro.
    eapply rtc_l. apply head_prim_step. auto_head_step. asimpl. apply rtc_refl.
  Qed.

  (* super boring lemma *)
  Lemma valrel_typed_cons_ren γ Δ : ∀ τ v v', valrel_typed (γ :: Δ) τ.[ren (+1)] v v' ⊣⊢ valrel_typed Δ τ v v'.
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
        iApply (lift_wand _ (valrel_typed (γ :: Δ) τ3.[ren (+1)])). iIntros (x x') "Hxx'". by iApply "IH1".
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
      destruct τ1; auto; destruct (Δ !! X) as [γ'|] eqn:eq; rewrite /= eq; try done.
      iIntros (v v'). iSplit.
      + iIntros "Hdes". iDestruct "Hdes" as (i) "(-> & -> & H)". iExists i. repeat iSplit; auto.
        iApply (inv_iff with "H"). repeat iModIntro. iSplit.
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi Hww']". iExists w, w'. iFrame "Hi". by iApply "IH1".
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi Hww']". iExists w, w'. iFrame "Hi". by iApply "IH1".
      + iIntros "Hdes". iDestruct "Hdes" as (i) "(-> & -> & H)". iExists i. repeat iSplit; auto.
        iApply (inv_iff with "H"). repeat iModIntro. iSplit.
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi Hww']". iExists w, w'. iFrame "Hi". by iApply "IH1".
        * iIntros "Hdes". iDestruct "Hdes" as (w w') "[Hi Hww']". iExists w, w'. iFrame "Hi". by iApply "IH1".
    - setoid_rewrite valrel_typed_TST_unfold; auto.
      destruct τ1; auto; destruct (Δ !! X) as [γ'|] eqn:eq; rewrite /= eq; try done.
      iIntros (w w'). iSplit.
      + iIntros "#H". iIntros (ps). iModIntro. iIntros "Hauth". iSpecialize ("H" $! ps with "Hauth"). iApply (wp_wand with "H").
        iIntros (v) "Hdes". iDestruct "Hdes" as (w1 w1' ps1) "(Hauth1 & -> & Hstep & H)". iExists w1, w1', ps1. repeat iSplit; auto.
        by iApply "IH1".
      + iIntros "#H". iIntros (ps). iModIntro. iIntros "Hauth". iSpecialize ("H" $! ps with "Hauth"). iApply (wp_wand with "H").
        iIntros (v) "Hdes". iDestruct "Hdes" as (w1 w1' ps1) "(Hauth1 & -> & Hstep & H)". iExists w1, w1', ps1. repeat iSplit; auto.
        by iApply "IH1".
  Qed.

  Lemma compat_runst Γ e e' τ :
    open_exprel_typed (subst (ren (+1)) <$> Γ) e e' (TST (TVar 0) τ.[ren (+1)]) →
    open_exprel_typed Γ (runst e) (runst e') τ.
  Proof.
    iIntros (Hee' Δ vs vs') "#Hvsvs'".
    change (runst ?e).[?σ] with (runst e.[σ]). simpl.
    iDestruct (ghost_empty ) as "#Hγ". iMod "Hγ". iDestruct "Hγ" as (γ) "Hauth".
    specialize (Hee' (γ :: Δ) vs vs').
    iDestruct Hee' as "Hee'". clear Hee'.
    rewrite -big_sepL3_fmap_l.
    change (Lam ?e) with (of_val $ LamV e).
    iApply (@wp_bind _ _ _ (fill_item $ AppRCtx _) (ectxi_lang_ctx_item _)).
    iApply wp_wand. iApply "Hee'". iApply (big_sepL3_impl with "Hvsvs'"). iModIntro. iIntros (τ' v v') "H". by iApply valrel_typed_cons_ren. iEval simpl.
    iIntros (v) "H". iDestruct "H" as (v') "[%Hsteps #Hvv']". iClear "Hvsvs' Hee'".
    iApply wp_step_later. apply head_prim_step. auto_head_step. asimpl. iNext. rewrite encode_empty_subst.
    iApply (@wp_bind _ _ _ (fill_item $ SndCtx) (ectxi_lang_ctx_item _)).
    rewrite valrel_typed_TST_unfold /=. iSpecialize ("Hvv'" $! [] with "Hauth"). simpl.
    iApply (wp_wand with "Hvv'"). iIntros (p) "H". iDestruct "H" as (r r' psf) "(Hauth & -> & %Hsteps' & #Hrr')".
    iApply wp_step_later. apply head_prim_step. auto_head_step. iNext.
    iApply wp_value'. iExists r'. iSplit.
    iPureIntro.
    change (Lam ?e) with (of_val (LamV e)).
    eapply rtc_transitive.
    by apply (@rtc_STLCmuVS_step_ctx (fill_item $ AppRCtx _) (ectxi_lang_ctx_item _)). simpl.
    eapply rtc_l. apply head_prim_step. auto_head_step. asimpl. rewrite encode_empty_subst.
    eapply rtc_transitive.
    by apply (@rtc_STLCmuVS_step_ctx (fill_item $ SndCtx) (ectxi_lang_ctx_item _)). simpl.
    change (Pair (of_val ?v1) (of_val ?v2)) with (of_val (PairV v1 v2)).
    apply rtc_once. apply head_prim_step. auto_head_step.
    by iApply valrel_typed_cons_ren.
  Qed.

  Lemma compat_equal Γ e1 e1' e2 e2' ρ τ :
    open_exprel_typed Γ e1 e1' (TSTref ρ τ) →
    open_exprel_typed Γ e2 e2' (TSTref ρ τ) →
    open_exprel_typed Γ (e1 = e2)%Eₙₒ (e1' = e2')%Eₙₒ TBool.
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (H1 H2 Δ vs vs') "#Hvsvs'".
    specialize (H1 Δ vs vs'). specialize (H2 Δ vs vs').
    iDestruct (H1 with "Hvsvs'") as "H1". clear H1. iDestruct (H2 with "Hvsvs'") as "H2". clear H2.
    iClear "Hvsvs'". iEval simpl.
    iApply (lift_bind' _ _ _ [BinOpLCtx _ _] [BinOpLCtx _ _] with "H1"). iEval simpl.
    iIntros (v1 v1') "#Hv1v1'". iClear "H1".
    iApply (lift_bind' _ _ _ [BinOpRCtx _ _] [BinOpRCtx _ _] with "H2"). iEval simpl.
    iIntros (v2 v2') "#Hv2v2'". simpl. iClear "H2".
    (* okay *)
    rewrite !valrel_typed_TSTRef_unfold. destruct ρ; auto; destruct (Δ !! X) as [γ|] eqn:eq; auto.
    iDestruct "Hv1v1'" as (i1) "(-> & -> & Hinv1)".
    iDestruct "Hv2v2'" as (i2) "(-> & -> & Hinv2)".
    iApply lift_step. apply head_prim_step. auto_head_step.
    iApply lift_step_later. apply head_prim_step. auto_head_step.
    iNext. simpl.
    change (Lit ?b)%Eₙₒ with (of_val b%Vₙₒ). iApply lift_val.
    rewrite valrel_typed_TBool_unfold. iExists _. iSplit; auto.
  Qed.

End compat_lemmas.
