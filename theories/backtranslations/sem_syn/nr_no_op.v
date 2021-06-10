From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst.
From st.lam Require Import nr_types lang typing tactics logrel.definitions logrel.generic.lift.
From st.backtranslations.un_syn Require Import logrel.definitions logrel.un_le_syn.fundamental universe.base.
From st.backtranslations.sem_syn Require Import nr_guard_assert.

Section nr_guard_assert_no_op.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Context (s : stuckness).

  Notation valrel_typed := (valrel_typed s).
  Notation exprel_typed := (exprel_typed s).

  Fixpoint nr_ga_eval (τ : nr_type) (ga : action) (v : val) : val :=
    (match τ with
     | NRTUnit => v
     | NRTBool => v
     | NRTInt => v
     | NRTProd τ1 τ2 => match v with
                       | PairV v1 v2 => PairV (nr_ga_eval τ1 ga v1) (nr_ga_eval τ2 ga v2)
                       | _ => ()
                       end
     | NRTSum τ1 τ2 => match v with
                      | InjLV v1 => InjLV (nr_ga_eval τ1 ga v1)
                      | InjRV v2 => InjRV (nr_ga_eval τ2 ga v2)
                      | _ => ()
                      end
     | NRTArrow τ1 τ2 => LamV ((ga_pair τ2 ga).{ren (+1)} (v.{ren (+1)} ((ga_pair τ1 (opp_action ga)).{ren (+1)} %0)))%Eₙₒ
     end)%Vₙₒ.

  Lemma nr_no_op_ga_help (τ : nr_type) : ∀ (ga : action) (v v' : val),
      valrel_typed τ v v' ⊢ ⌜ rtc lam_step (ga_pair τ ga v') (nr_ga_eval τ ga v') ⌝ ∧ valrel_typed τ v (nr_ga_eval τ ga v').
  Proof.
    induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 ] ;
      iIntros (ga v v') "#Hvv'".
    - rewrite valrel_typed_TUnit_unfold. iDestruct "Hvv'" as "[-> ->]". iSplit; auto.
      iPureIntro. destruct ga; by repeat auto_rtc_lam_step.
    - rewrite valrel_typed_TBool_unfold. iDestruct "Hvv'" as (b) "[-> ->]". iSplit; auto.
      iPureIntro. destruct ga; destruct b; repeat auto_rtc_lam_step.
    - rewrite valrel_typed_TInt_unfold. iDestruct "Hvv'" as (z) "[-> ->]". iSplit; auto.
      iPureIntro. destruct ga; repeat auto_rtc_lam_step. by assert ((z + 0%nat)%Z = z) as -> by lia.
    - rewrite !valrel_typed_TProd_unfold; fold nr_type_type.
      iDestruct "Hvv'" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
      iDestruct (IHτ1 ga v1 v1') as "IHτ1". iDestruct ("IHτ1" with "H1") as "[%Hs1 #Hr1]". clear IHτ1. iClear "H1 IHτ1".
      iDestruct (IHτ2 ga v2 v2') as "IHτ2". iDestruct ("IHτ2" with "H2") as "[%Hs2 #Hr2]". clear IHτ2. iClear "H2 IHτ2".
      iSplit.
      + iPureIntro. rewrite /= -!val_subst_valid. repeat auto_rtc_lam_step.
        eapply rtc_transitive. by apply (rtc_lam_step_ctx (fill_item (PairLCtx _))). simpl.
        by apply (rtc_lam_step_ctx (fill_item (PairRCtx _))).
      + iExists _, _, _, _. repeat iSplit; eauto.
    - rewrite !valrel_typed_TSum_unfold; fold nr_type_type.
      iDestruct "Hvv'" as (vi vi') "[(-> & -> & H) | (-> & -> & H)]".
      + iDestruct (IHτ1 ga vi vi') as "H'". iDestruct ("H'" with "H") as "[%Hs #Hr]". clear IHτ1 IHτ2. iClear "H H'". iSplit.
        * iPureIntro. rewrite /= -!val_subst_valid. repeat auto_rtc_lam_step.
          by apply (rtc_lam_step_ctx (fill [InjLCtx])).
        * iExists _, _. iLeft. repeat iSplit; eauto.
      + iDestruct (IHτ2 ga vi vi') as "H'". iDestruct ("H'" with "H") as "[%Hs #Hr]". clear IHτ1 IHτ2. iClear "H H'". iSplit.
        * iPureIntro. rewrite /= -!val_subst_valid. repeat auto_rtc_lam_step.
          by apply (rtc_lam_step_ctx (fill [InjRCtx])).
        * iExists _, _. iRight. repeat iSplit; eauto.
    - rewrite !valrel_typed_TArrow_unfold; fold nr_type_type.
      iSplitL.
      * iPureIntro. rewrite /= -!val_subst_valid. by auto_rtc_lam_step.
      * iModIntro. simpl. iIntros (w w') "#Hww". rewrite /= -!val_subst_valid.
        iApply lift_step. auto_lam_step. simplify_custom.
        iDestruct (IHτ1 (opp_action ga) w w') as "H". iDestruct ("H" with "Hww") as "[%Hs #Hr]". clear IHτ1. iClear "Hww H".
        iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _; AppRCtx _]).
        iSplitL. iApply lift_rtc_steps; eauto. by iApply lift_val.
        simpl. iIntros (r r') "#Hrr".
        iApply (lift_bind _ _ _ [] [AppRCtx _]). iSplitL. by iApply "Hvv'".
        iIntros (x x') "#Hxx". simpl.
        iDestruct (IHτ2 ga x x') as "H". iDestruct ("H" with "Hxx") as "[%Hs' #Hr']". clear IHτ2. iClear "H Hxx".
        iApply lift_rtc_steps; eauto. by iApply lift_val.
  Qed.

  Lemma nr_no_op_ga (τ : nr_type) : ∀ (ga : action) (v v' : val),
      valrel_typed τ v v' ⊢ exprel_typed τ v (ga_pair τ ga v').
  Proof.
    iIntros (ga v v') "Hvv'". iApply wp_value'.
    iExists (nr_ga_eval τ ga v'). by iApply nr_no_op_ga_help.
  Qed.

End nr_guard_assert_no_op.
