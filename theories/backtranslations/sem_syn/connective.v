From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst.
From st.lam Require Import types lang typing tactics logrel.definitions logrel.generic.lift.
From st.lam.lib Require Import fixlam universe.embed_project_two guard_assert_two universe.base.
From st.backtranslations.un_syn Require Import logrel.definitions logrel.un_le_syn.fundamental.

(* Defines connective lemma between the untyped and typed logic relations (the (untyped ≤ syntactically typed)-refinement) *)
(* Of the two refinements, this is the harder one; we need the additional guards/asserts *)
Section connective_un_le_syn.

  Instance rfn : refinement := un_le_syn.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Notation valrel_typed := (valrel_typed MaybeStuck).
  Notation exprel_typed := (exprel_typed MaybeStuck).

  Definition ap_Connective (τ : type) (asr prj : val) : iProp Σ :=
    ∀ (e e' : expr), (exprel e e' -∗ exprel_typed τ (asr e) (prj e')).

  Definition ge_Connective (τ : type) (grd emb : val) : iProp Σ :=
    ∀ (e e' : expr), (exprel_typed τ e e' -∗ exprel (grd e) (emb e')).

  Lemma ge_Connective_val (τ : type) (grd emb : val) : (∀ (v v' : val), valrel_typed τ v v' -∗ exprel (grd v) (emb v')) ⊢ ge_Connective τ grd emb.
  Proof. iIntros "H" (e e') "Hee'". iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _]). iFrame "Hee'". iIntros (v v') "HH". by iApply "H". Qed.

  Lemma ap_Connective_val (τ : type) (asr prj : val) : (∀ (v v' : val), valrel v v' -∗ exprel_typed τ (asr v) (prj v')) ⊢ ap_Connective τ asr prj.
  Proof. iIntros "H" (e e') "Hee'". iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _]). iFrame "Hee'". iIntros (v v') "HH". by iApply "H". Qed.

  Fixpoint big_sepL3 {PROP : bi} {A B C}
      (Φ : A → B → C → PROP) (l1 : list A) (l2 : list B) (l3 : list C) : PROP :=
    match l1, l2, l3 with
    | [], [], [] => emp
    | x1 :: l1, x2 :: l2, x3 :: l3 => Φ x1 x2 x3 ∗ big_sepL3 Φ l1 l2 l3
    | _, _,_ => False
    end%I.

  Lemma big_sepL3_lookup {A B C}
      (Φ : A → B → C → iProp Σ) l1 l2 l3 i x1 x2 x3 :
    l1 !! i = Some x1 → l2 !! i = Some x2 → l3 !! i = Some x3 →
    big_sepL3 Φ l1 l2 l3 ⊢ Φ x1 x2 x3.
  Proof.
    generalize dependent l3.
    generalize dependent l2.
    generalize dependent l1.
    induction i.
    - intros l1 l2 l3 H1 H2 H3. iIntros "H".
      destruct l1 as [|a1 k1]; inversion H1. destruct l2 as [|a2 k2]; inversion H2. destruct l3 as [|a3 k3]; inversion H3.
      simpl. iDestruct "H" as "[a b]". auto.
    - intros l1 l2 l3 H1 H2 H3.
      destruct l1 as [|a1 k1]; inversion H1. destruct l2 as [|a2 k2]; inversion H2. destruct l3 as [|a3 k3]; inversion H3.
      iIntros "H".
      iApply (IHi k1 k2 k3 H0 H4 H5).
      simpl. iDestruct "H" as "[a b]". auto.
  Qed.

  Lemma big_sepL3_length {A B C}
      (Φ : A → B → C → iProp Σ) l1 l2 l3 : big_sepL3 Φ l1 l2 l3 ⊢ ⌜ length l1 = length l2 ⌝ ∧ ⌜ length l2 = length l3 ⌝.
  Proof.
    generalize dependent l3.
    generalize dependent l2.
    generalize dependent l1.
    induction l1.
    - intros. destruct l2; destruct l3; auto.
    - intros. destruct l2; destruct l3; auto.
      iIntros "H". simpl. rewrite IHl1. iDestruct "H" as "[H %I]". iPureIntro. lia.
  Qed.

  Lemma connective_ep_ga (τ : type) (τs : list type) (pCnτ : Closed_n (length τs) τ) (eps gas : list val) :
    □ (big_sepL3
       (fun τ ep ga => ge_Connective τ (LamV (Fst (ga.{ren (+1)} ()) %0)) (LamV (Fst (ep.{ren (+1)} ()) %0)) ∧
                    ap_Connective τ (LamV (Snd (ga.{ren (+1)} ()) %0)) (LamV (Snd (ep.{ren (+1)} ()) %0))
       )%Eₙₒ
      ) τs eps gas ⊢ ge_Connective τ.[subst_list τs] (ga_pair Guard τ).{subst_list_val gas} (ep_pair Embed τ).{subst_list_val eps} ∧
                     ap_Connective τ.[subst_list τs] (ga_pair Assert τ).{subst_list_val gas} (ep_pair Project τ).{subst_list_val eps}.
  Proof.
    generalize dependent eps.
    generalize dependent gas.
    generalize dependent τs.
    induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τb IHτb | X ] ; intros τs pCnτ gas eps.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - specialize (IHτ1 τs ltac:(closed_solver) gas eps). specialize (IHτ2 τs ltac:(closed_solver) gas eps).
      iIntros "#H". iSplit.
      + simpl. iApply ge_Connective_val.
        iIntros (v v') "#Hvv'". iEval (rewrite valrel_typed_TArrow_unfold) in "Hvv'".
        (* step impl spec *)
        iEval (repeat rewrite -val_subst_valid).
        iApply lift_step_later. auto_lam_step. iEval simplify_custom.
        iApply lift_step. auto_lam_step. iEval simplify_custom. rewrite inject_Closed.
        (* step spec *)
        repeat assert (∀ e, Lam e = of_val $ LamV e) as ->; auto.
        iApply lift_step. apply inject_step'.
        (* val relation *)
        iApply lift_val. rewrite valrel_unfold. iExists TCArrow.
        iExists _. iSplitL "".  auto. iEval simpl. iExists _, _. iSplitL "". auto. iSplitL "". auto.
        (* *)
        repeat iModIntro. iIntros (w w') "#Hww'". fold valrel. asimpl. iEval repeat rewrite val_subst_valid.
        (* applying IHτ1 *)
        iApply (lift_bind  _ _ _ [AppRCtx _ ; AppRCtx _] [AppRCtx _ ; AppRCtx _]).
        iSplitL. iApply (IHτ1 with "H"). by iApply lift_val.
        (* *)
        iIntros (x x') "#Hxx'/=".
        (* using IHτ2 *)
        iApply (IHτ2 with "H").
        by iApply "Hvv'".
      + simpl. iApply ap_Connective_val.
        iIntros (v v') "#Hvv'".
        (* step impl spec *)
        iEval (repeat rewrite -val_subst_valid).
        iApply lift_step_later. auto_lam_step. iEval simplify_custom. rewrite extract_Closed.
        iApply lift_step. auto_lam_step. iEval simplify_custom.
        (* val relation *)
        repeat assert (∀ e, Lam e = of_val $ LamV e) as ->; auto. iApply lift_val.
        iEval rewrite valrel_typed_TArrow_unfold. repeat iModIntro.
        iIntros (w w') "#Hww'".
        (* step impl spec *)
        iEval (repeat rewrite val_subst_valid).
        iApply lift_step. auto_lam_step.
        iEval simplify_custom.
        iEval (repeat rewrite -val_subst_valid). iEval asimpl.
        rewrite extract_Closed.
        (* impl step *)
        iApply lift_step_later.
        repeat rewrite val_subst_valid.
        auto_lam_step. iEval simplify_custom.
        repeat rewrite val_subst_valid. repeat rewrite val_subst_comp. iEval asimpl.
        repeat rewrite -val_subst_valid. iEval asimpl.
        repeat rewrite val_subst_valid.
        (* extract val *)
        iApply (ectx_item_extract_val _ (AppLCtx _) [AppRCtx _] [AppLCtx _; AppRCtx _]); auto. iFrame "Hvv'".
        (*  *)
        iNext. iIntros (x x') "#Hxx'". iEval simpl. iDestruct "Hxx'" as (e e') "(-> & -> & Hee')".
        (* IH1 *)
        iApply (lift_bind _ _ _ [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _]).
        iSplitL. iApply IHτ1; auto. by iApply lift_val.
        (*  *)
        iIntros (x x') "#Hxx'". simpl.
        (* steps *)
        iApply lift_step_later. auto_lam_step. simplify_custom.
        iApply lift_step. auto_lam_step. simplify_custom.
        (* ih2 *)
        iApply IHτ2; auto. iNext. by iApply "Hee'".
    - (* TRec *)
      specialize (IHτb (TRec τb.[up (subst_list τs)] :: τs) ltac:(closed_solver)).
      iIntros "#H".
      (* lob induction *)
      iLöb as "IHLob".
      iSplit.
      + (* related values instead of expressions *)
        iApply ge_Connective_val.
        iIntros (v v') "#Hvv'".
        (* destruct value relation *)
        rewrite valrel_typed_unfold. iDestruct "Hvv'" as (w w') "(-> & -> & Hww')". fold (valrel_typed).
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iEval repeat rewrite -val_subst_valid. iEval simplify_custom.
        iApply lift_step. auto_lam_step.
        iEval repeat rewrite -val_subst_valid. iEval simplify_custom.
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iEval repeat rewrite -val_subst_valid. iEval simplify_custom.
        iApply lift_step. auto_lam_step.
        iEval repeat rewrite -val_subst_valid. iEval simplify_custom.
        (* *)
        iEval repeat rewrite FixArrow_subst. iEval asimpl.
        iEval repeat rewrite val_subst_valid. iEval rewrite fixgenTRec_subst fixgenTRecga_subst.
        (* Fixarrow steps on impl and spec side *)
        iApply lift_nsteps_later. apply nsteps_lam_step_ctx with (K := fill [AppLCtx _; FstCtx ; AppLCtx _]); first by apply ectx_lang_ctx. apply FixArrow_eval.
        iApply lift_rtc_steps. apply rtc_lam_step_ctx with (K := fill [AppLCtx _; FstCtx ; AppLCtx _]); first by apply ectx_lang_ctx. eapply nsteps_rtc. apply FixArrow_eval.
        iEval (simplify_custom). do 2 rewrite FixArrow_subst.
        iEval repeat rewrite val_subst_valid. iEval rewrite fixgenTRec_subst fixgenTRecga_subst.
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        iEval repeat rewrite -val_subst_valid.
        iEval simplify_custom.
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        (* *)
        iEval simplify_custom. rewrite inject_Closed.
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        iEval simplify_custom. rewrite inject_Closed. iEval repeat rewrite val_subst_valid.
        (* step on impl and spec side *)
        iApply lift_step. auto_lam_step.
        iApply lift_step_later. auto_lam_step.
        iEval (simpl; repeat rewrite to_of_val; simplify_option_eq).
        repeat rewrite val_subst_comp.
        (* using induction hypothesis *)
        do 2 (assert (∀ e, Lam e = of_val $ LamV e) as ->; auto).
        do 2 rewrite subst_list_val_cons.
        repeat iModIntro.
        iApply (lift_bind _ _ _ [FoldCtx] [FoldCtx ; AppRCtx _]).
        iSplitL. iApply IHτb. iModIntro.
        (* using ilob *)
        iSplitL. iEval (simpl) in "IHLob".
        iEval (repeat rewrite FixArrow_subst) in "IHLob".
        iEval (repeat rewrite val_subst_valid) in "IHLob".
        iEval (repeat rewrite val_subst_comp) in "IHLob".
        iEval (repeat rewrite fixgenTRecga_subst) in "IHLob".
        iEval (repeat rewrite fixgenTRec_subst) in "IHLob".
        iEval (asimpl) in "IHLob".
        iEval (simpl).
        iEval (repeat rewrite FixArrow_subst).
        iEval (repeat rewrite val_subst_valid).
        iEval (repeat rewrite fixgenTRecga_subst).
        iEval (repeat rewrite fixgenTRec_subst).
        iEval (repeat rewrite val_subst_comp).
        iEval (asimpl). auto.
        auto.
        iApply lift_val. iEval asimpl. iEval (asimpl) in "Hww'". auto.
        (* *)
        iIntros (x x') "Hxx'".
        iEval simpl. iApply lift_step.
        apply (inject_step _ (FoldV x')). auto. change (Fold x) with (of_val $ FoldV x). iApply lift_val.
        iEval rewrite valrel_unfold. iExists TCRec. iExists _. repeat iSplit; auto. rewrite /canon_tc_lift.
        iExists _, _; auto.
      + (* related values instead of expressions *)
        iApply ap_Connective_val.
        iIntros (v v') "#Hvv'".
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        iEval simplify_custom.
        do 2 iEval rewrite FixArrow_subst.
        iEval repeat rewrite val_subst_valid.
        iEval repeat rewrite val_subst_comp.
        iEval rewrite fixgenTRec_subst.
        iEval rewrite fixgenTRecga_subst.
        iEval asimpl.
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        iEval simplify_custom.
        do 2 iEval rewrite FixArrow_subst.
        iEval repeat rewrite val_subst_valid.
        iEval rewrite fixgenTRec_subst.
        iEval rewrite fixgenTRecga_subst.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        (* fixarrow steps *)
        iApply lift_nsteps_later. apply nsteps_lam_step_ctx with (K := fill [AppLCtx _; SndCtx ; AppLCtx _]); first by apply ectx_lang_ctx. apply FixArrow_eval.
        iApply lift_rtc_steps. apply rtc_lam_step_ctx with (K := fill [AppLCtx _; SndCtx ; AppLCtx _]); first by apply ectx_lang_ctx. eapply nsteps_rtc. apply FixArrow_eval.
        iEval (simplify_custom).
        do 2 rewrite FixArrow_subst.
        iEval repeat rewrite val_subst_valid.
        iEval rewrite fixgenTRec_subst.
        iEval rewrite fixgenTRecga_subst.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        iEval (simplify_custom). repeat rewrite extract_Closed. repeat rewrite inject_Closed.
        repeat rewrite FixArrow_subst.
        iEval repeat rewrite val_subst_valid.
        iEval rewrite fixgenTRec_subst.
        iEval rewrite fixgenTRecga_subst.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        iEval (simplify_custom).
        iEval repeat rewrite val_subst_valid.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        iEval (simplify_custom).
        repeat rewrite FixArrow_subst.
        iEval repeat rewrite val_subst_valid.
        iEval rewrite fixgenTRec_subst.
        iEval rewrite fixgenTRecga_subst.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        (* step on impl and spec side *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        iEval (simplify_custom).
        iEval repeat rewrite val_subst_valid.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        repeat rewrite FixArrow_subst.
        iEval repeat rewrite val_subst_valid.
        iEval rewrite fixgenTRec_subst.
        iEval rewrite fixgenTRecga_subst.
        iEval repeat rewrite val_subst_comp.
        iEval asimpl.
        iEval repeat rewrite -val_subst_valid. rewrite extract_Closed.
        iEval repeat rewrite val_subst_valid.
        (* v v' under unfold (extract trec) *)
        repeat iModIntro.
        iApply (ectx_item_extract_val _ UnfoldCtx [AppRCtx _; FoldCtx] [UnfoldCtx ; AppRCtx _; FoldCtx]); auto. iFrame "Hvv'".
        iIntros (x x') "Hdes". iDestruct "Hdes" as (w w') "(-> & -> & #Hww')". iEval simpl.
        (* STEP *)
        iApply lift_step_later. auto_lam_step.
        iApply lift_step. auto_lam_step.
        iEval (simplify_custom).
        (* ih *)
        iApply (lift_bind _ _ _ [FoldCtx] [FoldCtx]).
        iSplitL. iNext.
        do 2 (assert (∀ e, Lam e = of_val $ LamV e) as ->; auto).
        do 2 rewrite subst_list_val_cons. iApply IHτb. iModIntro.
        (* using ilob *)
        iSplitL. iEval (simpl) in "IHLob".
        iEval (repeat rewrite FixArrow_subst) in "IHLob".
        iEval (repeat rewrite val_subst_valid) in "IHLob".
        iEval (repeat rewrite val_subst_comp) in "IHLob".
        iEval (repeat rewrite fixgenTRecga_subst) in "IHLob".
        iEval (repeat rewrite fixgenTRec_subst) in "IHLob".
        iEval (asimpl) in "IHLob".
        iEval (simpl).
        iEval (repeat rewrite FixArrow_subst).
        iEval (repeat rewrite val_subst_valid).
        iEval (repeat rewrite fixgenTRecga_subst).
        iEval (repeat rewrite fixgenTRec_subst).
        iEval (repeat rewrite val_subst_comp).
        iEval (asimpl). auto.
        auto.
        iApply lift_val. iEval asimpl. iEval (asimpl) in "Hww'". auto.
        iNext.
        iIntros (x x') "#Hxx'". iEval simpl.
        change (Fold x) with (of_val $ FoldV x).
        change (Fold x') with (of_val $ FoldV x').
        iApply lift_val. iEval (asimpl) in "Hxx'".
        iEval rewrite valrel_typed_unfold. iExists _, _. repeat iSplit; auto.
        iEval asimpl. auto.
    - (* TVar *)
      iIntros "#H".
      destruct (TVar_subst_list_closed_n_length _ _ pCnτ) as [τ [eq1 ->]].
      iDestruct (big_sepL3_length with "H") as "[%H1 %H2]".
      destruct (eps !! X) as [ep |] eqn:eq2.
      destruct (gas !! X) as [ga |] eqn:eq3.
      iDestruct (big_sepL3_lookup _ _ _ _ X _ _ _ eq1 eq2 eq3 with "H") as "[a b]".
      iSplit.
      + asimpl.
        change (subst_list_val gas X) with ((ids X).[subst_list_val gas]). rewrite (Var_subst_list_val_lookup _ _ _ eq3).
        change (subst_list_val eps X) with ((ids X).[subst_list_val eps]). rewrite (Var_subst_list_val_lookup _ _ _ eq2).
        do 2 rewrite val_subst_valid. auto.
      + asimpl.
        change (subst_list_val gas X) with ((ids X).[subst_list_val gas]). rewrite (Var_subst_list_val_lookup _ _ _ eq3).
        change (subst_list_val eps X) with ((ids X).[subst_list_val eps]). rewrite (Var_subst_list_val_lookup _ _ _ eq2).
        do 2 rewrite val_subst_valid. auto.
      + exfalso.
        assert (length gas ≤ X). by apply lookup_ge_None.
        assert (X < length τs). by eapply lookup_lt_Some. lia.
      + exfalso.
        assert (length eps ≤ X). by apply lookup_ge_None.
        assert (X < length τs). by eapply lookup_lt_Some. lia.
  Admitted.

  Lemma guard_embed_connective (τ : type) (pCτ : Closed τ) (e e' : expr) :
    exprel_typed τ e e' ⊢ exprel (ga_pair Guard τ e) (ep_pair Embed τ e').
  Proof.
     cut (exprel_typed τ.[subst_list []] e e' ⊢ exprel ((ga_pair Guard τ.[subst_list []]).{subst_list_val [] } e) ((ep_pair Embed τ.[subst_list []]).{subst_list_val [] } e')).
     rewrite pCτ. asimpl. destruct τ; by asimpl.
     iDestruct (connective_ep_ga τ [] pCτ [] []) as "HHH/=".
     rewrite /ge_Connective. asimpl. iIntros "Hee'". iApply "HHH"; auto.
  Qed.

  Lemma assert_project_connective (τ : type) (pCτ : Closed τ) (e e' : expr) :
    exprel e e' ⊢ exprel_typed τ (ga_pair Assert τ e) (ep_pair Project τ e').
  Proof.
     cut (exprel e e' ⊢ exprel_typed τ.[subst_list []] ((ga_pair Assert τ.[subst_list []]).{subst_list_val [] } e) ((ep_pair Project τ.[subst_list []]).{subst_list_val [] } e')).
     rewrite pCτ. asimpl. destruct τ; by asimpl.
     iDestruct (connective_ep_ga τ [] pCτ [] []) as "HHH/=".
     rewrite /ap_Connective. asimpl. iIntros "Hee'". iApply "HHH"; auto.
  Qed.

End connective_un_le_syn.


(* Defines connective lemma between the untyped and typed logic relations (the (syntactically typed ≤ untyped)-refinement) *)
(* Of the two refinements, this is the harder one; we need the additional guards/asserts *)
Section connective_syn_le_un.

  Instance rfn' : refinement := syn_le_un.

  Print Instances refinement.

End connective_syn_le_un.
