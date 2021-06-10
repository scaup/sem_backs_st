(* We can prove weaker version, but it will not be modular...; no meaningful compatibility lemmas *)

From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst.
From st.lam Require Import types lang typing tactics logrel.definitions logrel.generic.lift.
From st.lam.lib Require Import fixlam universe.embed_project guard_assert universe.base.
From st.backtranslations.un_syn Require Import logrel.definitions logrel.un_le_syn.fundamental.

Section guard_assert_no_opV.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Context (s : stuckness).

  Notation valrel_typed := (valrel_typed s).
  Notation exprel_typed := (exprel_typed s).

  Fixpoint depth (v : val) : nat :=
    match v with
    | LamV e => 0
    | LitV v => 0
    | PairV v1 v2 => max (depth v1) (depth v2)
    | InjLV v => depth v
    | InjRV v => depth v
    | FoldV v => S (depth v)
    end.

  Definition NoOpGuard (τ : type) (grd : val) : iProp Σ :=
    ∀ (v v' : val), (valrel_typed τ v v') -∗ (▷^(depth v) exprel_typed τ v (grd v')).

  Definition NoOpAssert (τ : type) (asr : val) : iProp Σ :=
    ∀ (v v' : val), (valrel_typed τ v v') -∗ (▷^(depth v) exprel_typed τ v (asr v')).

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
        (* get lob induction and premisis for induction hyp *)
        iNext.
        (* apply IH *)
        repeat assert (∀ e, Lam e = of_val $ LamV e) as ->; auto.
        repeat rewrite subst_list_val_cons.
        iApply (lift_bind _ _ _ [FoldCtx] [FoldCtx]).
        iSplitL.
        iApply (IHτb (TRec τb.[up (subst_list τs)] :: τs)); auto. closed_solver. iSplitL; auto.
        { (* using ilob *)
          iEval (simpl) in "IHLob".
          iEval (repeat rewrite FixArrow_subst) in "IHLob".
          iEval (repeat rewrite val_subst_valid) in "IHLob".
          iEval (repeat rewrite val_subst_comp) in "IHLob".
          iEval (rewrite fixgenTRecga_subst) in "IHLob".
          iEval (asimpl) in "IHLob".
          iEval (simpl).
          iEval (repeat rewrite FixArrow_subst).
          iEval (repeat rewrite val_subst_valid).
          iEval (rewrite fixgenTRecga_subst).
          iEval (repeat rewrite val_subst_comp).
          iEval (asimpl).
          auto.
        }
        by asimpl.
        (* hmm *)
        iModIntro.
        iIntros (x x') "#Hxx'".
        iEval simpl.
        change (Fold x) with (of_val (FoldV x)). change (Fold x') with (of_val (FoldV x')).
        iApply lift_val.
        iEval rewrite valrel_typed_TRec_unfold.
        iExists x, x'. repeat iSplit; auto. by asimpl.
      + admit.
    - (* TVar *)
      iIntros "#H".
      destruct (TVar_subst_list_closed_n_length _ _ pCnτ) as [τ [eq1 ->]].
      iDestruct (big_sepL2_length with "H") as "%Hl".
      destruct (gas !! X) as [ga |] eqn:eq2; try by exfalso; (assert (length gas ≤ X); first by apply lookup_ge_None); (assert (X < length τs); first by eapply lookup_lt_Some); lia.
      iDestruct (big_sepL2_lookup _ _ _ _ _ _ eq1 eq2 with "H") as "[#a #b]".
      iSplit.
      + asimpl.
        change (subst_list_val gas X) with ((ids X).[subst_list_val gas]). rewrite (Var_subst_list_val_lookup _ _ _ eq2).
        rewrite val_subst_valid. auto.
      + asimpl.
        change (subst_list_val gas X) with ((ids X).[subst_list_val gas]). rewrite (Var_subst_list_val_lookup _ _ _ eq2).
        rewrite val_subst_valid. auto.
  Admitted.
