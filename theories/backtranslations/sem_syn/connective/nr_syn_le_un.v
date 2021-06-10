From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst.
From st.lam Require Import wkpre types nr_types lang typing tactics logrel.definitions logrel.generic.lift.
From st.backtranslations.un_syn Require Import universe.base.
From st.backtranslations.un_syn.logrel Require Import definitions syn_le_un.fundamental.
From st.backtranslations.sem_syn Require Import nr_embed_project.

(* Defines connective lemma between the untyped and typed logic relations (the (syntactically typed ≤ untyped)-refinement) *)
(* Of the two refinements, this is the easier one *)
Section connective_syn_le_un.

  Instance rfn' : refinement := syn_le_un.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Notation valrel_typed := (valrel_typed NotStuck).
  Notation exprel_typed := (exprel_typed NotStuck).

  Lemma nr_connective_ep_ga (τ : nr_type) : ⊢ ∀ (v v' : val),
      (valrel_typed τ v v' -∗ exprel (ep_pair τ Embed v) v') ∧
      (valrel v v' -∗ exprel_typed τ (ep_pair τ Project v) v').
  Proof.
    iInduction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 ] "IH";
      iIntros (v v').
    - iSplit.
      + iIntros "Hvv". rewrite valrel_typed_TUnit_unfold. iDestruct "Hvv" as "[-> ->]".
        iApply lift_step_later. eapply inject_step'. iApply lift_val.
        rewrite valrel_unfold. iExists TCUnit. by iExists ()%Vₙₒ.
      + iIntros "Hvv". simpl.
        iApply (bind_lift_extract [] [] v v' TCUnit). iSplitL. by iApply lift_val. iNext.
        iIntros (w w') "[-> ->]". iApply lift_val. by rewrite valrel_typed_TUnit_unfold.
    - iSplit.
      + iIntros "Hvv". rewrite valrel_typed_TBool_unfold. iDestruct "Hvv" as (b) "[-> ->]".
        iApply lift_step_later. eapply inject_step'. iApply lift_val.
        rewrite valrel_unfold. iExists TCBool. iExists b. repeat iSplit; auto. simpl. by iExists b.
      + iIntros "Hvv". simpl.
        iApply (bind_lift_extract [] [] v v' TCBool). iSplitL. by iApply lift_val. iNext.
        iIntros (w w') "des". iDestruct "des" as (b) "[-> ->]". iApply lift_val. rewrite valrel_typed_TBool_unfold. by iExists b.
    - iSplit.
      + iIntros "Hvv". rewrite valrel_typed_TInt_unfold. iDestruct "Hvv" as (i) "[-> ->]".
        iApply lift_step_later. eapply inject_step'. iApply lift_val.
        rewrite valrel_unfold. iExists TCInt. iExists i. repeat iSplit; auto. simpl. by iExists i.
      + iIntros "Hvv". simpl.
        iApply (bind_lift_extract [] [] v v'). iSplitL. by iApply lift_val. iNext.
        iIntros (w w') "des". iDestruct "des" as (i) "[-> ->]". iApply lift_val. rewrite valrel_typed_TInt_unfold. by iExists i.
    - iSplit.
      + iIntros "Hvv". rewrite valrel_typed_TProd_unfold.
        iDestruct "Hvv" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)". fold nr_type_type.
        iEval (rewrite /= -!val_subst_valid).
        do 5 ((iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite inject_Closed))).
        do 5 iNext.
        iApply (lift_bind _ _ _ [PairLCtx _; AppRCtx _] [PairLCtx _]). iSplitL. by iApply "IH".
        iIntros (w w') "#Hww". simpl.
        iApply (lift_bind _ _ _ [PairRCtx _; AppRCtx _] [PairRCtx _]). iSplitL. by iApply "IH1".
        iIntros (x x') "#Hxx". simpl.
        change (of_val ?v1, of_val ?v2)%Eₙₒ with (of_val (v1, v2)%Vₙₒ).
        iApply lift_step_later. apply inject_step'. iApply lift_val.
        iEval (rewrite valrel_unfold). iExists TCProd. iExists _. iSplit; eauto. repeat iExists _. iSplit; auto.
      + iIntros "#Hvv". iEval (simpl).
        iEval (rewrite /= -!val_subst_valid).
        (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite !extract_Closed)).
        iApply (bind_lift_extract [LetInCtx _] [] v v'). iSplitL. by iApply lift_val. iNext. iNext.
        iIntros (w w') "des". iDestruct "des" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)". simpl.
        do 5 (iApply lift_step_later; first auto_lam_step); iEval simplify_custom. repeat iNext.
        iApply (lift_bind _ _ _ [PairLCtx _] [PairLCtx _]). iSplitL. by iApply "IH".
        iIntros (w w') "#Hww". simpl.
        iApply (lift_bind _ _ _ [PairRCtx _] [PairRCtx _]). iSplitL. by iApply "IH1".
        iIntros (x x') "#Hxx". simpl.
        change (of_val ?v1, of_val ?v2)%Eₙₒ with (of_val (v1, v2)%Vₙₒ). iApply lift_val.
        iEval (rewrite valrel_typed_TProd_unfold). repeat iExists _. iSplit; auto.
    - iSplit.
      + iEval (rewrite valrel_typed_TSum_unfold); fold nr_type_type.
        iIntros "Hvv". iDestruct "Hvv" as (vi vi') "[(-> & -> & Hvivi) | (-> & -> & Hvivi)]".
        * iClear "IH1". iEval (rewrite /= -!val_subst_valid).
          do 2 (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite inject_Closed)). do 2 iNext.
          iApply (lift_bind _ _ _ [InjLCtx; AppRCtx _] [InjLCtx]). iSplitL. iApply ("IH" with "Hvivi").
          iIntros (v v') "Hvv". simpl. change (InjL (of_val ?v)) with (of_val (InjLV v)).
          iApply lift_step_later. apply inject_step'. iApply lift_val.
          iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; eauto. repeat iExists _. iLeft. iSplit; auto.
        * iClear "IH". iEval (rewrite /= -!val_subst_valid).
          do 2 (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite inject_Closed)). do 2 iNext.
          iApply (lift_bind _ _ _ [InjRCtx; AppRCtx _] [InjRCtx]). iSplitL. iApply ("IH1" with "Hvivi").
          iIntros (v v') "Hvv". simpl. change (InjR (of_val ?v)) with (of_val (InjRV v)).
          iApply lift_step_later. apply inject_step'. iApply lift_val.
          iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; eauto. repeat iExists _. iRight. iSplit; auto.
      + iIntros "Hvv".
        rewrite /= -!val_subst_valid.
        (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        iApply (bind_lift_extract [CaseCtx _ _] [] v v'). iSplitL. by iApply lift_val. iNext.
        iIntros (w w') "des". iDestruct "des" as (vi vi') "[(-> & -> & Hvivi) | (-> & -> & Hvivi)]"; simpl.
        * (iApply lift_step_later; first auto_lam_step); iEval simplify_custom. iNext.
          iApply (lift_bind _ _ _ [InjLCtx] [InjLCtx]). iSplitL. by iApply "IH".
          iIntros (w w') "Hww". simpl. change (InjL (of_val ?v)) with (of_val (InjLV v)). iApply lift_val.
          rewrite valrel_typed_TSum_unfold. iExists _, _. iLeft. auto.
        * (iApply lift_step_later; first auto_lam_step); iEval simplify_custom. iNext.
          iApply (lift_bind _ _ _ [InjRCtx] [InjRCtx]). iSplitL. by iApply "IH1".
          iIntros (w w') "Hww". simpl. change (InjR (of_val ?v)) with (of_val (InjRV v)). iApply lift_val.
          rewrite valrel_typed_TSum_unfold. iExists _, _. iRight. auto.
    - iSplit.
      + iIntros "#Hvv". rewrite valrel_typed_TArrow_unfold; fold nr_type_type.
        rewrite /= -!val_subst_valid.
        (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; try rewrite inject_Closed).
        change (Lam ?e) with (of_val $ LamV e).
        iApply lift_step_later. apply inject_step'. iApply lift_val. repeat iNext.
        rewrite valrel_unfold. iExists TCArrow. iExists _. iSplit; auto. simpl.
        iExists _. repeat iSplit; eauto.
        iNext. iModIntro.
        iIntros (w w') "#Hww". asimpl.
        (* iApply (lift_anti_step _ _ _ (v' w')). apply head_prim_step. auto_head_step. *)
        iApply (lift_bind _ _ _ [AppRCtx _; AppRCtx _] [AppRCtx _]). iSplitL. by iApply "IH".
        iIntros (x x') "#Hxx". simpl.
        iApply (lift_bind _ _ _ [AppRCtx _] []). simpl. iSplitL. by iApply "Hvv".
        iIntros (y y') "#Hyy". simpl.
        by iApply "IH1".
      + iIntros "#Hvv".
        rewrite /= -!val_subst_valid.
        (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        change (Lam ?e) with (of_val $ LamV e). iApply lift_val.
        rewrite valrel_typed_TArrow_unfold. iModIntro.
        iIntros (w w') "#Hww".
        (iApply lift_step_later; first auto_lam_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        iApply (bind_lift_extract [AppLCtx _ ; AppRCtx _] [AppLCtx _]). iSplitL. by iApply lift_val.
        iNext. iIntros (f f') "#Hff".
        iDestruct "Hff" as (e) "(%eq & #Hff)". iEval simpl.
        iApply (lift_bind _ _ _ [AppRCtx _; AppRCtx _] [AppRCtx _]). iSplitL. by iApply "IH".
        iIntros (x x') "#Hxx". iEval simpl. rewrite eq.
        (iApply lift_step_later; first auto_lam_step); iEval simplify_custom. iNext.
        iApply (lift_bind _ _ _ [AppRCtx _] []). iSplitL. by iApply "Hff".
        iIntros (y y') "Hyy". simpl. by iApply "IH1".
  Qed.

End connective_syn_le_un.
