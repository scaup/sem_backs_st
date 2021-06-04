From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst big_op_three.
From st.lam.lib Require Import fixlam universe.nr_embed_project nr_guard_assert universe.base universe.paths.
From st.lam Require Import wkpre types nr_types lang typing tactics logrel.definitions logrel.generic.lift.
From st.backtranslations.un_syn Require Import logrel.definitions logrel.un_le_syn.fundamental.

(* Defines connective lemma between the untyped and typed logic relations (the (untyped ≤ syntactically typed)-refinement) *)
(* Of the two refinements, this is the harder one; we need the additional guards/asserts *)
Section nr_connective_un_le_syn.

  Instance rfn : refinement := un_le_syn.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Notation valrel_typed := (valrel_typed MaybeStuck).
  Notation exprel_typed := (exprel_typed MaybeStuck).

  Lemma nr_connective_ep_ga (τ : nr_type) : ⊢ ∀ (v v' : val),
      (valrel_typed τ v v' -∗ exprel (ga_pair τ Guard v) (ep_pair τ Embed v')) ∧
      (valrel v v' -∗ exprel_typed τ (ga_pair τ Assert v) (ep_pair τ Project v')).
  Proof.
    iInduction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 ] "IH";
      iIntros (v v').
    - iSplit.
      + iIntros "Hvv". rewrite valrel_typed_TUnit_unfold. iDestruct "Hvv" as "[-> ->]".
        iApply lift_step. eapply inject_step'.
        iApply (lift_step_later _ _ _ ()%Vₙₒ). auto_lam_step.
        iNext. iApply lift_val.
        rewrite valrel_unfold. iExists TCUnit. by iExists ()%Vₙₒ.
      + iIntros "Hvv".
        iApply lift_step_later. auto_lam_step. simplify_custom.
        iApply (ectx_item_extract_val _ (SeqCtx _) [] []); auto. iNext. iFrame "Hvv".
        iIntros (w w') "[-> ->]". simpl.
        iApply lift_step_later. auto_lam_step. simplify_custom.
        change ()%Eₙₒ with (of_val ()%Vₙₒ). iApply lift_val.
        by rewrite valrel_typed_TUnit_unfold.
    - iSplit.
      + iIntros "Hvv". rewrite valrel_typed_TBool_unfold. iDestruct "Hvv" as (b) "[-> ->]".
        iApply lift_step. eapply inject_step'.
        iApply (lift_step_later _ _ _ b%Vₙₒ). auto_lam_step.
        iNext. change (Lit b) with (of_val (LitV b)). iApply lift_val.
        rewrite valrel_unfold. iExists TCBool. iExists b. simpl. auto.
      + iIntros "Hvv".
        iApply lift_step_later. auto_lam_step. simplify_custom.
        iApply (ectx_item_extract_val _ (IfCtx _ _) [] []); auto. iNext. iFrame "Hvv".
        iIntros (w w') "des". iDestruct "des" as (b) "[-> ->]". simpl.
        iApply lift_step_later. destruct b; auto_lam_step. simplify_custom.
        change (Lit b)%Eₙₒ with (of_val b%Vₙₒ). iApply lift_val.
        rewrite valrel_typed_TBool_unfold. by iExists b.
    - iSplit.
      + iIntros "Hvv". rewrite valrel_typed_TInt_unfold. iDestruct "Hvv" as (z) "[-> ->]".
        iApply lift_step. eapply inject_step'.
        iApply (lift_step_later _ _ _ z%Vₙₒ). auto_lam_step.
        iNext. change (Lit z) with (of_val (LitV z)). iApply lift_val.
        rewrite valrel_unfold. iExists TCInt. iExists z. simpl. auto.
      + iIntros "Hvv".
        iApply lift_step_later. auto_lam_step. simplify_custom.
        iApply (ectx_item_extract_val _ (BinOpLCtx _ _) [] []); auto. iNext. iFrame "Hvv".
        iIntros (w w') "des". iDestruct "des" as (z) "[-> ->]". simpl.
        iApply lift_step_later. auto_lam_step. simplify_custom.
        assert ((z + 0%nat)%Z = z) as -> by lia. change (Lit z)%Eₙₒ with (of_val z%Vₙₒ). iApply lift_val.
        rewrite valrel_typed_TInt_unfold. by iExists z.
    - iSplit.
      + iIntros "Hvv". rewrite valrel_typed_TProd_unfold; fold nr_type_type. iDestruct "Hvv" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
        iEval (rewrite /= -!val_subst_valid).
        do 5 ((iApply lift_step; first auto_lam_step); iEval (simplify_custom; (try rewrite inject_Closed))).
        do 5 ((iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite inject_Closed))).
        do 5 iNext.
        iApply (lift_bind _ _ _ [PairLCtx _] [PairLCtx _; AppRCtx _]). iSplitL. by iApply "IH".
        iIntros (w w') "#Hww". simpl.
        iApply (lift_bind _ _ _ [PairRCtx _] [PairRCtx _; AppRCtx _]). iSplitL. by iApply "IH1".
        iIntros (x x') "#Hxx". simpl.
        change (of_val ?v1, of_val ?v2)%Eₙₒ with (of_val (v1, v2)%Vₙₒ).
        iApply lift_step. apply inject_step'. iApply lift_val.
        iEval (rewrite valrel_unfold). iExists TCProd. iExists _. iSplit; eauto. repeat iExists _. iSplit; auto.
      + iIntros "#Hvv". iEval (simpl).
        iEval (rewrite /= -!val_subst_valid).
        (iApply lift_step; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)).
        (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        (* ectx_item_extract_val is not general enough here *)
        iEval (rewrite valrel_unfold /=) in "Hvv".
        iDestruct "Hvv" as (tc w') "[-> #Hvv]".
        destruct (decide (tc = TCProd)) as [-> | neq].
        * iDestruct "Hvv" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
          iApply lift_rtc_steps. apply (rtc_lam_step_ctx (fill [LetInCtx _])). eapply rtc_l. apply extract_step. apply eval_same_tc. iEval simpl.
          do 4 (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)). repeat iNext.
          do 5 (iApply lift_step; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)).
          iApply (lift_bind _ _ _ [PairLCtx _] [PairLCtx _]). iSplitL. by iApply "IH".
          iIntros (x x') "#Hxx". simpl.
          iApply (lift_bind _ _ _ [PairRCtx _] [PairRCtx _]). iSplitL. by iApply "IH1".
          iIntros (y y') "#Hyy". simpl.
          change (of_val ?v1, of_val ?v2)%Eₙₒ with (of_val (v1, v2)%Vₙₒ). iApply lift_val.
          iEval (rewrite valrel_typed_TProd_unfold). repeat iExists _. iSplit; auto.
        * iApply (wp_bind (fill [LetInCtx _])). iRename "Hvv" into "HHH". stuck_cases tc.
    - iSplit.
      + iEval (rewrite valrel_typed_TSum_unfold); fold nr_type_type.
        iIntros "Hvv". iDestruct "Hvv" as (vi vi') "[(-> & -> & Hvivi) | (-> & -> & Hvivi)]".
        * iClear "IH1". iEval (rewrite /= -!val_subst_valid).
          do 2 (iApply lift_step; first auto_lam_step); iEval (simplify_custom; (try rewrite inject_Closed)).
          do 2 (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite inject_Closed)). do 2 iNext.
          iApply (lift_bind _ _ _ [InjLCtx] [InjLCtx; AppRCtx _]). iSplitL. iApply ("IH" with "Hvivi").
          iIntros (v v') "Hvv". simpl. change (InjL (of_val ?v)) with (of_val (InjLV v)).
          iApply lift_step. apply inject_step'. iApply lift_val.
          iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; eauto. repeat iExists _. iLeft. iSplit; auto.
        * iClear "IH". iEval (rewrite /= -!val_subst_valid).
          do 2 (iApply lift_step; first auto_lam_step); iEval (simplify_custom; (try rewrite inject_Closed)).
          do 2 (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite inject_Closed)). do 2 iNext.
          iApply (lift_bind _ _ _ [InjRCtx] [InjRCtx; AppRCtx _]). iSplitL. iApply ("IH1" with "Hvivi").
          iIntros (v v') "Hvv". simpl. change (InjR (of_val ?v)) with (of_val (InjRV v)).
          iApply lift_step. apply inject_step'. iApply lift_val.
          iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; eauto. repeat iExists _. iRight. iSplit; auto.
      + iIntros "Hvv".
        rewrite /= -!val_subst_valid.
        (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        (iApply lift_step; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)).
        iApply (ectx_item_extract_val _ (CaseCtx _ _) [] [CaseCtx _ _]); auto. iFrame "Hvv". iEval simpl.
        iIntros (w w') "des". iDestruct "des" as (vi vi') "[(-> & -> & Hvivi) | (-> & -> & Hvivi)]".
        * (iApply lift_step_later; first auto_lam_step); iEval simplify_custom. iNext.
          (iApply lift_step; first auto_lam_step); iEval simplify_custom.
          iApply (lift_bind _ _ _ [InjLCtx] [InjLCtx]). iSplitL. by iApply "IH".
          iIntros (w w') "Hww". simpl. change (InjL (of_val ?v)) with (of_val (InjLV v)). iApply lift_val.
          rewrite valrel_typed_TSum_unfold. iExists _, _. iLeft.  auto.
        * (iApply lift_step_later; first auto_lam_step); iEval simplify_custom. iNext.
          (iApply lift_step; first auto_lam_step); iEval simplify_custom.
          iApply (lift_bind _ _ _ [InjRCtx] [InjRCtx]). iSplitL "Hvivi". by iApply "IH1".
          iIntros (w w') "Hww". simpl. change (InjR (of_val ?v)) with (of_val (InjRV v)). iApply lift_val.
          rewrite valrel_typed_TSum_unfold. iExists _, _. iRight. auto.
    - iSplit.
      + iIntros "#Hvv". rewrite valrel_typed_TArrow_unfold; fold nr_type_type.
        rewrite /= -!val_subst_valid.
        (iApply lift_step_later; first auto_lam_step); iEval simplify_custom. iNext.
        (iApply lift_step; first auto_lam_step); iEval (simplify_custom; try rewrite inject_Closed).
        change (Lam ?e) with (of_val $ LamV e).
        iApply lift_step. apply inject_step'. iApply lift_val.
        rewrite valrel_unfold. iExists TCArrow. iExists _. iSplit; auto.
        iExists _. repeat iSplit; eauto. iNext. iModIntro.
        iIntros (w w') "#Hww". asimpl.
        (iApply lift_step; first auto_lam_step); iEval simplify_custom.
        iApply (lift_bind _ _ _ [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _]).
        iSplitL. by iApply "IH".
        iIntros (x x') "#Hxx". simpl.
        iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _]).
        iSplitL. by iApply "Hvv".
        iIntros (y y') "#Hyy". simpl.
        by iApply "IH1".
      + iIntros "#Hvv".
        rewrite /= -!val_subst_valid.
        (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        (iApply lift_step; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)).
        change (Lam ?e) with (of_val $ LamV e). iApply lift_val.
        rewrite valrel_typed_TArrow_unfold. iModIntro.
        iIntros (w w') "#Hww".
        (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        (iApply lift_step; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)).
        iApply (ectx_item_extract_val _ (AppLCtx _) [AppRCtx _] [AppLCtx _; AppRCtx _]); auto. iFrame "Hvv".
        iIntros (f f') "#Hff".
        iApply (lift_bind _ _ _ [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _]).
        iSplitL. by iApply "IH".
        iIntros (x x') "#Hxx".
        iDestruct "Hff" as (e) "(-> & #Hee)". iEval simpl.
        (iApply lift_step_later; first auto_lam_step); iEval simplify_custom. iNext.
        iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _]). iSplitL. by iApply "Hee".
        iIntros (y y') "Hyy". simpl. by iApply "IH1".
  Qed.

  Lemma nr_guard_embed_connective (τ : nr_type) (v v' : val) :
    valrel_typed τ v v' ⊢ exprel (ga_pair τ Guard v) (ep_pair τ Embed v').
  Proof. iIntros "H". by iApply nr_connective_ep_ga. Qed.

  Lemma nr_assert_project_connective (τ : nr_type) (v v' : val) :
    valrel v v' ⊢ exprel_typed τ (ga_pair τ Assert v) (ep_pair τ Project v').
  Proof. iIntros "H". by iApply nr_connective_ep_ga. Qed.

End nr_connective_un_le_syn.
