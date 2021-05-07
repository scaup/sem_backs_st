From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst.
From st.lam Require Import types lang typing tactics logrel.definitions logrel.generic.lift.
From st.lam.lib Require Import fixlam universe.embed_project guard_assert universe.base.
From st.backtranslations.un_syn Require Import logrel.definitions logrel.un_le_syn.fundamental.

(* Note: Proving *)
(* ∀ (v v' : val), (valrel_typed τ v v') ⊢ (exprel_typed τ v (guard τ v')) *)
(* does not work out as termination of guard τ v' depends on complete relatedness of valrel_typed τ v v'. *)

Section guard_assert_no_op.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Context (s : stuckness).

  Notation valrel_typed := (valrel_typed s).
  Notation exprel_typed := (exprel_typed s).

  Definition NoOpGuard (τ : type) (grd : val) : iProp Σ :=
    ∀ (v v' : val), (valrel_typed τ v v') -∗ (exprel_typed τ v (grd v')).

  Definition NoOpAssert (τ : type) (asr : val) : iProp Σ :=
    ∀ (v v' : val), (valrel_typed τ v v') -∗ (exprel_typed τ v (asr v')).

  Lemma no_op_ga (τ : type) (τs : list type) (pCnτ : Closed_n (length τs) τ) (gas : list val) :
    □ ([∗ list] τ ; ga ∈ τs ; gas ,
                            NoOpGuard τ (LamV (Fst (ga.{ren (+1)} ()) %0)) ∧
                            NoOpAssert τ (LamV (Snd (ga.{ren (+1)} ()) %0)))%Eₙₒ
      ⊢ NoOpGuard τ.[subst_list τs] (ga_pair Guard τ).{subst_list_val gas} ∧
    NoOpAssert τ.[subst_list τs] (ga_pair Assert τ).{subst_list_val gas}.
  Proof.
    generalize dependent gas.
    generalize dependent τs.
    induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τb IHτb | X ] ; intros τs pCnτ gas.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - specialize (IHτb (τb.[TRec τb.[subst_list τs]/] :: τs)). iIntros "#H".
      iLöb as "IHlob".
      iSplit.
      + rewrite /NoOpGuard. iIntros (v v') "#Hvv'".
        iEval rewrite /exprel_typed /=. iEval rewrite /lift. 


    - (* TArrow *)
      iIntros "#H".
      iDestruct (IHτ1 τs ltac:(closed_solver) gas with "H") as "[IHτ1 IHτ2]".
      iSplit.
      + iIntros (v v') "#Hvv'". iEval simpl.
        (* step right side *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        iEval repeat rewrite -val_subst_valid; asimpl; repeat rewrite val_subst_valid.
        (* *)
        repeat assert (∀ e, Lam e = of_val $ LamV e) as ->; auto.
        iApply lift_val.
        iEval rewrite valrel_typed_TArrow_unfold.
        do 2 iModIntro.
        iIntros (w w') "#Hww'".
        iSpecialize ("IHτ1" $! w w' with "Hww'").
        (* step right side *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        iEval repeat rewrite -val_subst_valid; asimpl; repeat rewrite val_subst_valid.
        (* ih1 *)
        iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _; AppRCtx _]).
        iSplitL. iApply "IHτ1"; auto. closed_solver.
        (*  *)
        iIntros (x x') "Hxx'". iEval simpl.
        (*  *)
        iEval (rewrite valrel_typed_TArrow_unfold) in "Hvv'".
        iApply (lift_bind _ _ _ [] [AppRCtx _]).
        iSplitL. by iApply "Hvv'". iIntros (y y') "Hyy'". simpl.
        iApply IHτ2; auto. closed_solver.
      + iIntros (v v') "#Hvv'". iEval simpl.
        (* step right side *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        iEval repeat rewrite -val_subst_valid; asimpl; repeat rewrite val_subst_valid.
        (* *)
        repeat assert (∀ e, Lam e = of_val $ LamV e) as ->; auto.
        iApply lift_val.
        iEval rewrite valrel_typed_TArrow_unfold.
        iModIntro. iIntros (w w') "#Hww'".
        (* step right side *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        iEval repeat rewrite -val_subst_valid; asimpl; repeat rewrite val_subst_valid.
        (* ih1 *)
        iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _; AppRCtx _]).
        iSplitL. iApply IHτ1; auto. closed_solver.
        (*  *)
        iIntros (x x') "Hxx'". iEval simpl.
        (*  *)
        iEval (rewrite valrel_typed_TArrow_unfold) in "Hvv'".
        iApply (lift_bind _ _ _ [] [AppRCtx _]).
        iSplitL. by iApply "Hvv'". iIntros (y y') "Hyy'". simpl.
        iApply IHτ2; auto. closed_solver.
    - (* TRec *)
      iIntros "#H".
      iLöb as "IHLob".
      iSplit.
      + iIntros (v v') "Hvv'".
        (* step *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        rewrite FixArrow_subst.
        iEval repeat rewrite -val_subst_valid. iEval asimpl.
        iEval repeat rewrite val_subst_valid.
        iEval rewrite fixgenTRecga_subst.
        (* step *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        rewrite FixArrow_subst.
        iEval repeat rewrite -val_subst_valid. iEval asimpl.
        iEval repeat rewrite val_subst_valid.
        iEval rewrite fixgenTRecga_subst.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        (* fixarrow steps *)
        iApply lift_rtc_steps. apply rtc_lam_step_ctx with (K := fill [AppLCtx _; FstCtx ; AppLCtx _]); first by apply ectx_lang_ctx. eapply nsteps_rtc. apply FixArrow_eval.
        iEval simpl.
        (* step *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        rewrite FixArrow_subst.
        iEval repeat rewrite -val_subst_valid. iEval asimpl.
        iEval repeat rewrite val_subst_valid.
        iEval rewrite fixgenTRecga_subst.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        (* step *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        iEval repeat rewrite -val_subst_valid. iEval asimpl.
        (* step *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        iEval repeat rewrite val_subst_valid.
        (* step *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        (* destruct val rel *)
        iEval (rewrite valrel_typed_TRec_unfold) in "Hvv'". iDestruct "Hvv'" as (w w') "(-> & -> & #Hww')".
        iEval repeat rewrite val_subst_valid.
        (* step *)
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        repeat rewrite FixArrow_subst.
        iEval repeat rewrite val_subst_valid.
        iEval rewrite fixgenTRecga_subst.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        repeat rewrite FixArrow_subst.
        iEval repeat rewrite val_subst_valid.
        iEval rewrite fixgenTRecga_subst.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        (* apply IH *)
        repeat assert (∀ e, Lam e = of_val $ LamV e) as ->; auto.
        repeat rewrite subst_list_val_cons.


  Admitted.

