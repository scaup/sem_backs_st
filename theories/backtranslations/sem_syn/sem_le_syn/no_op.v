From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst.
From st.STLCmuVS Require Import lang virt_steps types typing tactics logrel.definitions logrel.generic.lift reducibility.
From st Require Import resources.

Section VirtStep_no_op.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Context (s : stuckness).

  Lemma VirtStep_no_op_help :
    ∀ τ v v', valrel_typed s τ v v' ⊢ valrel_typed s τ v (VirtStepped v').
  Proof.
    iLöb as "IHlob".
    iIntros (τ).
    iInduction τ as [] "IH";
      iIntros (v v') "#Hvv'".
    - rewrite !valrel_typed_TUnit_unfold.
      by iDestruct "Hvv'" as "[-> ->]/=".
    - rewrite !valrel_typed_TBool_unfold.
      iDestruct "Hvv'" as (b) "[-> ->]/=". by iExists _.
    - rewrite !valrel_typed_TInt_unfold.
      iDestruct "Hvv'" as (z) "[-> ->]/=". by iExists _.
    - rewrite !valrel_typed_TProd_unfold.
      iDestruct "Hvv'" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)/=".
      repeat iExists _; repeat iSplit; auto; [by iApply "IH"| by iApply "IH1"].
    - rewrite !valrel_typed_TSum_unfold.
      iDestruct "Hvv'" as (vi vi') "[(-> & -> & #H) | (-> & -> & #H)]/=".
      + repeat iExists _. iLeft. repeat iSplit; auto. by iApply "IH".
      + repeat iExists _. iRight. repeat iSplit; auto. by iApply "IH1".
    - rewrite !valrel_typed_TArrow_unfold.
      iModIntro. iIntros (w w') "#Hww'".
      iSpecialize ("IH" $! w w' with "Hww'"). iSpecialize ("Hvv'" $! w (VirtStepped w') with "IH").
      iApply (wp_wand with "Hvv'"). iIntros (r) "Hdes". iDestruct "Hdes" as (r') "[%Hsteps #Hrr']".
      iSpecialize ("IH1" $! r r' with "Hrr'").
      iExists (VirtStepped r'). iFrame "IH1".
      iPureIntro.
      destruct (dec_expr_reducibility (v' (VirtStepped w'))) as [ vl eq | red | stuck ]; [inversion eq| |].
      * assert (head_reducible (v' (VirtStepped w')) ()).
        { apply prim_head_reducible; auto.
          apply ectxi_language_sub_redexes_are_values.
          intros. destruct Ki; simpl in H; try by inversion H.
          inversion H. subst. eexists _. by rewrite /= to_of_val.
          inversion H. subst. eexists _. by rewrite /= to_of_val. }
        assert (STLCmuVS_head_reducible (v' (VirtStepped w'))). by apply STLCmuVS_prim_head_red.
        destruct H0 as [p hd].
        inversion hd; subst. assert (LamV e1 = v') as <-. by apply of_val_inj.
        eapply rtc_l. auto_STLCmuVS_step. simplify_custom.
        change (Lam e1) with (of_val (LamV e1)).
        eapply rtc_transitive. apply (rtc_STLCmuVS_step_ctx (fill [AppRCtx _; VirtStepCtx])). apply VirtStep_eval. simpl.
        eapply rtc_transitive. by apply (rtc_STLCmuVS_step_ctx (fill [VirtStepCtx])).
        apply VirtStep_eval.
      * exfalso. inversion Hsteps; subst.
        -- assert (abs : to_val (v' (VirtStepped w')) = Some r'). by rewrite -to_of_val H1. inversion abs.
        -- destruct stuck. eapply H2. apply H.
    - rewrite !valrel_typed_TRec_unfold.
      iDestruct "Hvv'" as (w w') "(-> & -> & #Hww')".
      iExists _,_. repeat iSplit; auto. by iApply "IHlob".
    - by rewrite !valrel_typed_TVar_unfold.
  Qed.

  Lemma VirtStep_no_op :
    ∀ τ v v', valrel_typed s τ v v' ⊢ exprel_typed s τ v (VirtStep v').
  Proof. iIntros (τ v v') "Hvv'". iApply lift_rtc_steps. apply VirtStep_eval. iApply lift_val. by iApply VirtStep_no_op_help. Qed.

  Lemma VirtStep_no_op_expr :
    ∀ τ e e', exprel_typed s τ e e' ⊢ exprel_typed s τ e (VirtStep e').
  Proof. iIntros (τ e e') "Hee'". iApply (lift_bind'' _ [] [VirtStepCtx] with "Hee'"). iIntros (v v') "Hvv'". by iApply VirtStep_no_op. Qed.

End VirtStep_no_op.

