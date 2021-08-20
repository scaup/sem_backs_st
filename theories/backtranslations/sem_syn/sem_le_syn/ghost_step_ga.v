From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst.
From st.STLCmuVS Require Import lang virt_steps typing tactics logrel.definitions logrel.generic.lift reducibility wkpre fixarrow.
From st.STLCmu Require Import types.
From st Require Import resources.
From st.backtranslations.sem_syn Require Import guard_assert.

Section VirtStep_ga.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Notation s := MaybeStuck.

  Definition TP (τ : type) (grd asr : val) : iProp Σ :=
    (∀ (v v' : val), (valrel_typed s τ v v' -∗ exprel_typed s τ (VirtStep v) (grd v'))) ∗
    (∀ (v v' : val), (valrel_typed s τ v v' -∗ exprel_typed s τ (VirtStep v) (asr v'))).

  Lemma VirtStep_ga_help :
    ∀ (τ : type) (τs : list type) (pCnτ : Closed_n (length τs) τ) (gas : list val),
        □ ([∗ list] τ ; ga ∈ τs ; gas , TP τ (LamV (Fst (ga.{ren (+1)} ()) %0)%Eₙₒ) (LamV (Snd (ga.{ren (+1)} ()) %0))%Eₙₒ) ⊢
          ∀ ga v v', valrel_typed s τ.[subst_list τs] v v' -∗ exprel_typed s τ.[subst_list τs] (VirtStep v) ((ga_pair ga τ).{subst_list_val gas} v').
  Proof.
    iLöb as "IHlob".
    iIntros (τ). iInduction τ as [] "IH".
    - iClear "IHlob". iIntros (τs pτ gas) "#Hgas".
      iIntros (ga v v') "#Hvv'".
      rewrite valrel_typed_TUnit_unfold /=. iDestruct "Hvv'" as "[-> ->]".
      destruct ga.
      + iApply lift_step_later. auto_STLCmuVS_step. simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        change ()%Eₙₒ with (of_val ()%Vₙₒ). iApply lift_val.
        by rewrite valrel_typed_TUnit_unfold /=.
      + iApply lift_step_later. auto_STLCmuVS_step. simplify_custom. iNext.
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        change ()%Eₙₒ with (of_val ()%Vₙₒ). iApply lift_val.
        by rewrite valrel_typed_TUnit_unfold /=.
    - iClear "IHlob". iIntros (τs pτ gas) "#Hgas".
      iIntros (ga v v') "#Hvv'".
      rewrite valrel_typed_TBool_unfold /=. iDestruct "Hvv'" as (b) "[-> ->]".
      destruct ga.
      + iApply lift_step_later. auto_STLCmuVS_step. simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        change (Lit b)%Eₙₒ with (of_val (b)%Vₙₒ). iApply lift_val.
        rewrite valrel_typed_TBool_unfold /=. by iExists _.
      + iApply lift_step_later. auto_STLCmuVS_step. simplify_custom. iNext.
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        iApply lift_step. destruct b; auto_STLCmuVS_step. simplify_custom.
        change (Lit b)%Eₙₒ with (of_val (b)%Vₙₒ). iApply lift_val.
        rewrite valrel_typed_TBool_unfold /=. by iExists _.
    - iClear "IHlob". iIntros (τs pτ gas) "#Hgas".
      iIntros (ga v v') "#Hvv'".
      rewrite valrel_typed_TInt_unfold /=. iDestruct "Hvv'" as (z) "[-> ->]".
      destruct ga.
      + iApply lift_step_later. auto_STLCmuVS_step. simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        change (Lit z)%Eₙₒ with (of_val (z)%Vₙₒ). iApply lift_val.
        rewrite valrel_typed_TInt_unfold /=. by iExists _.
      + iApply lift_step_later. auto_STLCmuVS_step. simplify_custom. iNext.
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. simplify_custom. replace (z + 0%nat)%Z with z by lia.
        change (Lit z)%Eₙₒ with (of_val (z)%Vₙₒ). iApply lift_val.
        rewrite valrel_typed_TInt_unfold /=. by iExists _.
    - setoid_rewrite <- val_subst_valid. iClear "IHlob". iIntros (τs pτ gas) "#Hgas".
      assert (pτ1 : Closed_n (length τs) τ1) by closed_solver. iSpecialize ("IH" $! τs pτ1 gas with "Hgas"). clear pτ1.
      assert (pτ2 : Closed_n (length τs) τ2) by closed_solver. iSpecialize ("IH1" $! τs pτ2 gas with "Hgas"). clear pτ2.
      iIntros (ga v v') "#Hvv'". rewrite valrel_typed_TProd_unfold.
      iDestruct "Hvv'" as (v1 v2 v1' v2') "(-> & -> & H1 & H2)".
      iSpecialize ("IH" $! ga v1 v1' with "H1"). iSpecialize ("IH1" $! ga v2 v2' with "H2").
      iApply lift_step_later. auto_STLCmuVS_step.
      iApply lift_step. auto_STLCmuVS_step. iEval (rewrite -!val_subst_valid; simplify_custom).
      iApply lift_step. auto_STLCmuVS_step. iEval (simplify_custom).
      iApply lift_step. auto_STLCmuVS_step. iEval (simplify_custom).
      iApply lift_step. auto_STLCmuVS_step. iEval (simplify_custom).
      iApply lift_step. auto_STLCmuVS_step. iEval (simplify_custom).
      iNext.
      iApply (lift_bind'' _ [PairLCtx _] [PairLCtx _] with "IH"). iIntros (w1 w1') "#Hw1w1'".
      iApply (lift_bind'' _ [PairRCtx _] [PairRCtx _] with "IH1"). iIntros (w2 w2') "#Hw2w2'".
      simpl. change (Pair (of_val ?w1) (of_val ?w2)) with (of_val (PairV w1 w2)). iApply lift_val.
      rewrite valrel_typed_TProd_unfold. repeat iExists _. auto.
    - setoid_rewrite <- val_subst_valid. iClear "IHlob". iIntros (τs pτ gas) "#Hgas".
      assert (pτ1 : Closed_n (length τs) τ1) by closed_solver. iSpecialize ("IH" $! τs pτ1 gas with "Hgas"). clear pτ1.
      assert (pτ2 : Closed_n (length τs) τ2) by closed_solver. iSpecialize ("IH1" $! τs pτ2 gas with "Hgas"). clear pτ2.
      iIntros (ga v v') "#Hvv'". rewrite valrel_typed_TSum_unfold.
      iDestruct "Hvv'" as (vi vi') "[(-> & -> & H) | (-> & -> & H)]".
      + iSpecialize ("IH" $! ga vi vi' with "H"). iClear "IH1".
        iApply lift_step_later. auto_STLCmuVS_step.
        iApply lift_step. auto_STLCmuVS_step. iEval (rewrite -!val_subst_valid; simplify_custom).
        iApply lift_step. auto_STLCmuVS_step. iEval (simplify_custom).
        iApply (lift_bind'' _ [InjLCtx] [InjLCtx] with "IH"). iNext. iIntros (wi wi') "#Hwiwi'".
        simpl. change (InjL (of_val ?w)) with (of_val (InjLV w)). iApply lift_val. rewrite valrel_typed_TSum_unfold.
        repeat iExists _. iLeft. auto.
      + iSpecialize ("IH1" $! ga vi vi' with "H"). iClear "IH".
        iApply lift_step_later. auto_STLCmuVS_step.
        iApply lift_step. auto_STLCmuVS_step. iEval (rewrite -!val_subst_valid; simplify_custom).
        iApply lift_step. auto_STLCmuVS_step. iEval (simplify_custom).
        iApply (lift_bind'' _ [InjRCtx] [InjRCtx] with "IH1"). iNext. iIntros (wi wi') "#Hwiwi'".
        simpl. change (InjR (of_val ?w)) with (of_val (InjRV w)). iApply lift_val. rewrite valrel_typed_TSum_unfold.
        repeat iExists _. iRight. auto.
    - setoid_rewrite <- val_subst_valid. iClear "IHlob". iIntros (τs pτ gas) "#Hgas".
      assert (pτ1 : Closed_n (length τs) τ1) by closed_solver. iSpecialize ("IH" $! τs pτ1 gas with "Hgas"). clear pτ1.
      assert (pτ2 : Closed_n (length τs) τ2) by closed_solver. iSpecialize ("IH1" $! τs pτ2 gas with "Hgas"). clear pτ2.
      iIntros (ga v v') "#Hvv'". rewrite valrel_typed_TArrow_unfold.
      iApply lift_rtc_steps_impl. apply VirtStep_eval.
      iApply lift_step. auto_STLCmuVS_step. iEval (simplify_custom). iEval (rewrite -!val_subst_valid; simplify_custom).
      change (Lam ?e) with (of_val (LamV e)). iApply lift_val. rewrite valrel_typed_TArrow_unfold. iModIntro. iIntros (w w') "#Hww'".
      iSpecialize ("IH" $! (opp_action ga) w w' with "Hww'").
      iApply lift_step. auto_STLCmuVS_step. iEval (simplify_custom).
      destruct v; iEval simpl; try by (iApply wp_stuck; head_stuck_solver).
      iApply lift_step_later. auto_STLCmuVS_step. iEval (simplify_custom).
      change (Lam ?e) with (of_val (LamV e)). iEval (rewrite !val_subst_valid).
      iApply (lift_bind'' _ [AppRCtx _; VirtStepCtx] [AppRCtx _; AppRCtx _]).
      iEval (rewrite -!val_subst_valid). iApply "IH". iNext.
      iIntros (r r') "#Hrr'". iEval simpl. iSpecialize ("Hvv'" $! r r' with "Hrr'").
      iApply (lift_bind'' _ [VirtStepCtx] [AppRCtx _] with "Hvv'"). iIntros (s s') "#Hss'/=".
      iEval (rewrite -!val_subst_valid). by iApply "IH1".
    - setoid_rewrite <- val_subst_valid. iIntros (τs pμτ gas) "#Hgas".
      assert (p : Closed_n (length (TRec τ.[up (subst_list τs)] :: τs)) τ) by closed_solver.
      iSpecialize ("IH" $! (TRec τ.[up (subst_list τs)] :: τs) p). clear p.
      iIntros (ga v v') "#Hvv'". rewrite valrel_typed_TRec_unfold.
      iDestruct "Hvv'" as (w w') "(-> & -> & #Hww')".
      iApply lift_step_later. auto_STLCmuVS_step. iNext. iEval simplify_custom.
      iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
      destruct ga; iEval simpl.
      + iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iEval rewrite FixArrow_subst -!val_subst_valid. iEval asimpl.
        iEval rewrite !val_subst_valid fixgenTRecga_subst.
        iApply lift_rtc_steps. apply rtc_STLCmuVS_step_ctx with (K := fill [AppLCtx _; FstCtx ; AppLCtx _]); first by apply ectx_lang_ctx. eapply nsteps_rtc. apply FixArrow_eval.
        iEval (simplify_custom). rewrite FixArrow_subst.
        iEval rewrite !val_subst_valid. iEval rewrite fixgenTRecga_subst.
        rewrite !val_subst_comp. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step.
        iEval rewrite -!val_subst_valid. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step.
        iEval rewrite !val_subst_valid. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iEval rewrite -!val_subst_valid. iEval simplify_custom. iEval rewrite !FixArrow_subst.
        iEval rewrite !val_subst_valid fixgenTRecga_subst !val_subst_comp. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iEval rewrite val_subst_valid val_subst_comp. iEval simplify_custom.
        iEval rewrite !FixArrow_subst !val_subst_valid fixgenTRecga_subst !val_subst_comp.
        iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iEval (change (Lam ?e) with (of_val $ LamV e)). rewrite subst_list_val_cons.
        iApply (lift_bind'' _ [FoldCtx] [FoldCtx]).
        repeat setoid_rewrite val_subst_valid. iApply "IH". iFrame "Hgas". iModIntro.
        { iClear "IH". iSpecialize ("IHlob" $! (TRec τ) τs pμτ gas with "Hgas"). iEval (rewrite /TP).
          iSplitL.
          - asimpl. iIntros (v v') "#Hvv'". iSpecialize ("IHlob" $! Guard v v' with "Hvv'").
            simpl. rewrite !FixArrow_subst -!val_subst_valid. asimpl.
            rewrite !val_subst_valid !fixgenTRecga_subst !val_subst_comp. asimpl. auto.
          - asimpl. iIntros (v v') "#Hvv'". iSpecialize ("IHlob" $! Assert v v' with "Hvv'").
            simpl. rewrite !FixArrow_subst -!val_subst_valid. asimpl.
            rewrite !val_subst_valid !fixgenTRecga_subst !val_subst_comp. asimpl. auto.
        }
        by asimpl.
        iIntros (v v') "#Hvv/=". change (Fold (of_val ?v)) with (of_val (FoldV v)). iApply lift_val.
        rewrite valrel_typed_TRec_unfold. iExists _, _. repeat iSplit; auto. by asimpl.
      + iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iEval rewrite FixArrow_subst -!val_subst_valid. iEval asimpl.
        iEval rewrite !val_subst_valid fixgenTRecga_subst.
        iApply lift_rtc_steps. apply rtc_STLCmuVS_step_ctx with (K := fill [AppLCtx _; SndCtx ; AppLCtx _]); first by apply ectx_lang_ctx. eapply nsteps_rtc. apply FixArrow_eval.
        iEval (simplify_custom). rewrite FixArrow_subst.
        iEval rewrite !val_subst_valid. iEval rewrite fixgenTRecga_subst.
        rewrite !val_subst_comp. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step.
        iEval rewrite -!val_subst_valid. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step.
        iEval rewrite !val_subst_valid. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iEval rewrite -!val_subst_valid. iEval simplify_custom. iEval rewrite !FixArrow_subst.
        iEval rewrite !val_subst_valid fixgenTRecga_subst !val_subst_comp. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iEval rewrite val_subst_valid val_subst_comp. iEval simplify_custom.
        iEval rewrite !FixArrow_subst !val_subst_valid fixgenTRecga_subst !val_subst_comp.
        iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iEval (change (Lam ?e) with (of_val $ LamV e)). rewrite subst_list_val_cons.
        iApply (lift_bind'' _ [FoldCtx] [FoldCtx]).
        repeat setoid_rewrite val_subst_valid. iApply "IH". iFrame "Hgas". iModIntro.
        { iClear "IH". iSpecialize ("IHlob" $! (TRec τ) τs pμτ gas with "Hgas"). iEval (rewrite /TP).
          iSplitL.
          - asimpl. iIntros (v v') "#Hvv'". iSpecialize ("IHlob" $! Guard v v' with "Hvv'").
            simpl. rewrite !FixArrow_subst -!val_subst_valid. asimpl.
            rewrite !val_subst_valid !fixgenTRecga_subst !val_subst_comp. asimpl. auto.
          - asimpl. iIntros (v v') "#Hvv'". iSpecialize ("IHlob" $! Assert v v' with "Hvv'").
            simpl. rewrite !FixArrow_subst -!val_subst_valid. asimpl.
            rewrite !val_subst_valid !fixgenTRecga_subst !val_subst_comp. asimpl. auto.
        }
        by asimpl.
        iIntros (v v') "#Hvv/=". change (Fold (of_val ?v)) with (of_val (FoldV v)). iApply lift_val.
        rewrite valrel_typed_TRec_unfold. iExists _, _. repeat iSplit; auto. by asimpl.
    - (* TVar *) iClear "IHlob".
      iIntros (τs pX gas) "#Hgas".
      destruct (TVar_subst_list_closed_n_length _ _ pX) as [τ [eq1 ->]].
      iDestruct (big_sepL2_length with "Hgas") as "%H1".
      destruct (gas !! X) as [ga |] eqn:eq2.
      + rewrite /TP.
        iDestruct (big_sepL2_lookup _ τs gas X _ _ eq1 eq2 with "Hgas") as "[a b]".
        iIntros (ac). destruct ac.
        * iEval asimpl. change (subst_list_val gas X) with ((ids X).[subst_list_val gas]). rewrite (Var_subst_list_val_lookup _ _ _ eq2). by rewrite val_subst_valid.
        * iEval asimpl. change (subst_list_val gas X) with ((ids X).[subst_list_val gas]). rewrite (Var_subst_list_val_lookup _ _ _ eq2). by rewrite val_subst_valid.
      + exfalso.
        assert (length gas ≤ X). by apply lookup_ge_None.
        assert (X < length τs). by eapply lookup_lt_Some. lia.
  Qed.

  Lemma val_subst_ids v : v.{ids} = v.
  Proof.
    induction v; asimpl; try done.
    - by rewrite IHv1 IHv2.
    - by rewrite IHv.
    - by rewrite IHv.
    - by rewrite IHv.
  Qed.

  Lemma VirtStep_ga (τ : type) (pCτ : Closed τ) ga (v v' : val) :
    valrel_typed s τ v v' ⊢ exprel_typed s τ (VirtStep v) (ga_pair ga τ v').
  Proof.
    cut (valrel_typed s τ.[subst_list []] v v' ⊢ exprel_typed s τ.[subst_list []] (VirtStep v) ((ga_pair ga τ.[subst_list []]).{subst_list_val [] } v')).
    rewrite pCτ. asimpl. by rewrite val_subst_ids.
    iIntros "#Hvv'".
    iDestruct (VirtStep_ga_help τ [] pCτ []) as "H/=". asimpl. by iApply "H".
  Qed.

  Lemma VirtStep_ga_expr (τ : type) (pCτ : Closed τ) ga (e e' : expr) :
    exprel_typed s τ e e' ⊢ exprel_typed s τ (VirtStep e) (ga_pair ga τ e').
  Proof.
    iIntros "Hee'".
    iApply (lift_bind'' _ [VirtStepCtx] [AppRCtx _] with "Hee'").
    iIntros (v v') "#Hvv'". by iApply VirtStep_ga.
  Qed.

End VirtStep_ga.
