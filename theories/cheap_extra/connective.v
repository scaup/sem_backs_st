From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.prelude Require Import autosubst big_op_three.
From st.STLCmuVS Require Import lang typing tactics logrel.definitions logrel.generic.lift.
From st.STLCmu Require Import types.
From st.STLCmuVS.lib Require Import fixarrow.
From st.backtranslations.un_syn Require Import logrel.definitions logrel.syn_le_un.compat_lemmas universe.base universe.paths.
From st.backtranslations.sem_syn Require Import embed_project guard_assert.
From st Require Import resources.

Section connective_un_le_syn.

  Instance rfn : refinement := syn_le_un.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Notation valrel_typed := (valrel_typed MaybeStuck).
  Notation exprel_typed := (exprel_typed MaybeStuck).

  Definition pa_Connective (τ : type) (prj asr : val) : iProp Σ :=
    ∀ (v v' : val), (valrel v v' -∗ exprel_typed τ (prj v) (asr v')).

  Definition eg_Connective (τ : type) (emb grd : val) : iProp Σ :=
    ∀ (v v' : val), (valrel_typed τ v v' -∗ exprel (emb v) (grd v')).

  Lemma connective_ep_ga (τ : type) (τs : list type) (pCnτ : Closed_n (length τs) τ) (eps gas : list val) :
    □ (big_sepL3
       (fun τ ep ga => eg_Connective τ (LamV (Fst (ep.{ren (+1)} ()) %0)) (LamV (Fst (ga.{ren (+1)} ()) %0)) ∧
                    pa_Connective τ (LamV (Snd (ep.{ren (+1)} ()) %0)) (LamV (Snd (ga.{ren (+1)} ()) %0))
       )%Eₙₒ
      ) τs eps gas ⊢ eg_Connective τ.[subst_list τs] (ep_pair Embed τ).{subst_list_val eps} (ga_pair Guard τ).{subst_list_val gas} ∧
                     pa_Connective τ.[subst_list τs] (ep_pair Project τ).{subst_list_val eps} (ga_pair Assert τ).{subst_list_val gas}.
  Proof.
    generalize dependent gas.
    generalize dependent eps.
    generalize dependent τs.
    induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τb IHτb | X ] ; intros τs pCnτ eps gas.
    - iIntros "Hl". iEval (rewrite /eg_Connective /pa_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iIntros (v v') "Hvv". rewrite valrel_typed_TUnit_unfold. iDestruct "Hvv" as "[-> ->]".
        iApply (lift_step _ _ _ _ ()%Vₙₒ). auto_STLCmuVS_step.
        iApply lift_step_later. eapply inject_step'.
        iNext. iApply lift_val.
        rewrite valrel_unfold. iExists TCUnit. by iExists ()%Vₙₒ.
      + iIntros (v v') "Hvv".
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        iApply (bind_lift_extract [] [ SeqCtx _] _ _ TCUnit).
        iSplitL "Hvv". by iApply lift_val.
        iNext. iIntros (w w') "[-> ->]". simpl.
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        change ()%Eₙₒ with (of_val ()%Vₙₒ). iApply lift_val.
        by rewrite valrel_typed_TUnit_unfold.
    - iIntros "Hl". iEval (rewrite /eg_Connective /pa_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iIntros (v v') "Hvv". rewrite valrel_typed_TBool_unfold. iDestruct "Hvv" as (b) "[-> ->]".
        iApply lift_step_later. eapply inject_step'.
        iApply (lift_step _ _ _ _ (b)%Vₙₒ). auto_STLCmuVS_step.
        change (Lit b)%Eₙₒ with (of_val (LitV b)%Vₙₒ). iApply lift_val.
        rewrite valrel_unfold. iExists TCBool. iExists _. iSplit; auto. by iExists _.
      + iIntros (v v') "Hvv".
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        iApply (bind_lift_extract [] [ IfCtx _ _] _ _ TCBool).
        iSplitL "Hvv". by iApply lift_val.
        iNext. iIntros (w w') "des". iDestruct "des" as (b) "[-> ->]". simpl.
        iApply lift_step. destruct b; auto_STLCmuVS_step. simplify_custom.
        change (Lit b)%Eₙₒ with (of_val b%Vₙₒ). iApply lift_val.
        rewrite valrel_typed_TBool_unfold. by iExists b.
    - iIntros "Hl". iEval (rewrite /eg_Connective /pa_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iIntros (v v') "Hvv". rewrite valrel_typed_TInt_unfold. iDestruct "Hvv" as (z) "[-> ->]".
        iApply lift_step_later. eapply inject_step'.
        iApply (lift_step _ _ _ _ z%Vₙₒ). auto_STLCmuVS_step.
        iNext. change (Lit z) with (of_val (LitV z)). iApply lift_val.
        rewrite valrel_unfold. iExists TCInt. iExists z. simpl. auto.
      + iIntros (v v') "Hvv".
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        iApply (bind_lift_extract [] [ BinOpLCtx _ _] _ _ _).
        iSplitL "Hvv". by iApply lift_val. iNext.
        iIntros (w w') "des". iDestruct "des" as (z) "[-> ->]". simpl.
        iApply lift_step. auto_STLCmuVS_step. simplify_custom.
        assert ((z + 0%nat)%Z = z) as -> by lia. change (Lit z)%Eₙₒ with (of_val z%Vₙₒ). iApply lift_val.
        rewrite valrel_typed_TInt_unfold. by iExists z.
    - iIntros "#Hl". iEval (rewrite /eg_Connective /pa_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iIntros (v v') "Hvv". rewrite valrel_typed_TProd_unfold. iDestruct "Hvv" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
        do 5 ((iApply lift_step; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite inject_Closed))).
        do 5 ((iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite inject_Closed))).
        do 5 iNext.
        iApply (lift_bind _ _ _ [PairLCtx _; AppRCtx _] [PairLCtx _] ). iSplitL.
        rewrite !val_subst_valid. by iApply (IHτ1 τs ltac:(closed_solver) with "Hl").
        iIntros (w w') "#Hww". simpl.
        iApply (lift_bind _ _ _ [PairRCtx _; AppRCtx _] [PairRCtx _] ). iSplitL.
        rewrite !val_subst_valid. by iApply (IHτ2 τs ltac:(closed_solver) with "Hl").
        iIntros (x x') "#Hxx". simpl.
        change (of_val ?v1, of_val ?v2)%Eₙₒ with (of_val (v1, v2)%Vₙₒ).
        iApply lift_step_later. apply inject_step'. iApply lift_val.
        iEval (rewrite valrel_unfold). iExists TCProd. iExists _. iSplit; eauto. repeat iExists _. iSplit; auto.
      + iIntros (v v') "#Hvv". iEval (simpl).
        (iApply lift_step; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite extract_Closed)).
        (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        iEval (rewrite valrel_unfold /=) in "Hvv".
        iDestruct "Hvv" as (tc w') "[-> #Hvv]".
        destruct (decide (tc = TCProd)) as [-> | neq].
        * iDestruct "Hvv" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
          iApply lift_rtc_steps_impl. apply (rtc_STLCmuVS_step_ctx (fill [LetInCtx _])). eapply rtc_l. apply extract_step. apply eval_same_tc. iEval simpl.
          do 4 (iApply lift_step; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite extract_Closed)). repeat iNext.
          do 5 (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite extract_Closed)).
          iApply (lift_bind _ _ _ [PairLCtx _] [PairLCtx _]). iSplitL.
          rewrite !val_subst_valid. by iApply (IHτ1 τs ltac:(closed_solver) with "Hl").
          repeat iNext. iIntros (x x') "#Hxx". simpl.
          iApply (lift_bind _ _ _ [PairRCtx _] [PairRCtx _]). iSplitL.
          rewrite !val_subst_valid. by iApply (IHτ2 τs ltac:(closed_solver) with "Hl").
          iIntros (y y') "#Hyy". simpl.
          change (of_val ?v1, of_val ?v2)%Eₙₒ with (of_val (v1, v2)%Vₙₒ). iApply lift_val.
          iEval (rewrite valrel_typed_TProd_unfold). repeat iExists _. iSplit; auto.
        * iApply (wp_bind (fill [LetInCtx _])).
          iApply wkpre.wp_step_later. apply extract_step.
          iApply wkpre.wp_rtc_steps. by apply eval_diff_tc.
          iApply wp_Ω.
    - iIntros "#Hl". iEval (rewrite /eg_Connective /pa_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iEval (setoid_rewrite valrel_typed_TSum_unfold).
        iIntros (v v') "Hvv". iDestruct "Hvv" as (vi vi') "[(-> & -> & Hvivi) | (-> & -> & Hvivi)]".
        * clear IHτ2.
          do 2 (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite inject_Closed)).
          do 2 (iApply lift_step; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite inject_Closed)). do 2 iNext.
          iApply (lift_bind _ _ _ [InjLCtx; AppRCtx _] [InjLCtx]). iSplitL.
          rewrite !val_subst_valid. by iApply (IHτ1 τs ltac:(closed_solver) with "Hl").
          iIntros (v v') "Hvv". simpl. change (InjL (of_val ?v)) with (of_val (InjLV v)).
          iApply lift_step_later. apply inject_step'. iApply lift_val.
          iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; eauto. repeat iExists _. iLeft. iSplit; auto.
        * clear IHτ1.
          do 2 (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite inject_Closed)).
          do 2 (iApply lift_step; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite inject_Closed)). do 2 iNext.
          iApply (lift_bind _ _ _ [InjRCtx; AppRCtx _] [InjRCtx]). iSplitL.
          rewrite !val_subst_valid. by iApply (IHτ2 τs ltac:(closed_solver) with "Hl").
          iIntros (v v') "Hvv". simpl. change (InjR (of_val ?v)) with (of_val (InjRV v)).
          iApply lift_step_later. apply inject_step'. iApply lift_val.
          iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; eauto. repeat iExists _. iRight. iSplit; auto.
      + iIntros (v v') "Hvv".
        (iApply lift_step; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite extract_Closed)).
        (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        iApply (bind_lift_extract [CaseCtx _ _ ] [ CaseCtx _ _] _ _ _).
        iSplitL "Hvv". by iApply lift_val. iNext.
        iIntros (w w') "des". iDestruct "des" as (vi vi') "[(-> & -> & Hvivi) | (-> & -> & Hvivi)]".
        * (iApply lift_step_later; first auto_STLCmuVS_step); iEval simplify_custom. iNext.
          (iApply lift_step; first auto_STLCmuVS_step); iEval simplify_custom.
          iApply (lift_bind _ _ _ [InjLCtx] [InjLCtx]). iSplitL.
          rewrite !val_subst_valid. by iApply (IHτ1 τs ltac:(closed_solver) with "Hl").
          iIntros (w w') "Hww". simpl. change (InjL (of_val ?v)) with (of_val (InjLV v)). iApply lift_val.
          rewrite valrel_typed_TSum_unfold. iExists _, _. iLeft.  auto.
        * (iApply lift_step_later; first auto_STLCmuVS_step); iEval simplify_custom. iNext.
          (iApply lift_step; first auto_STLCmuVS_step); iEval simplify_custom.
          iApply (lift_bind _ _ _ [InjRCtx] [InjRCtx]). iSplitL "Hvivi".
          rewrite !val_subst_valid. by iApply (IHτ2 τs ltac:(closed_solver) with "Hl").
          iIntros (w w') "Hww". simpl. change (InjR (of_val ?v)) with (of_val (InjRV v)). iApply lift_val.
          rewrite valrel_typed_TSum_unfold. iExists _, _. iRight. auto.
    - specialize (IHτ1 τs ltac:(closed_solver) eps gas). specialize (IHτ2 τs ltac:(closed_solver) eps gas).
      iIntros "#H". iSplit.
      + iIntros (v v') "#Hvv'". iEval (rewrite valrel_typed_TArrow_unfold) in "Hvv'".
        (* step impl spec *)
        iEval (repeat rewrite -val_subst_valid).
        iApply lift_step_later. auto_STLCmuVS_step.
        iEval (rewrite -!val_subst_valid; simplify_custom).
        iApply lift_step. auto_STLCmuVS_step.
        iEval (rewrite -!val_subst_valid; simplify_custom).
        rewrite inject_Closed.
        (* step spec *)
        repeat assert (∀ e, Lam e = of_val $ LamV e) as ->; auto.
        iApply lift_step_later. apply inject_step'.
        (* val relation *)
        iApply lift_val. rewrite valrel_unfold. fold valrel. iExists TCArrow.
        iExists _. iSplitL ""; auto. iEval simpl. iExists _. iSplitL ""; auto.
        (* *)
        repeat iModIntro. iIntros (w w') "#Hww'". asimpl.
        change (Lam ?e) with (of_val (LamV e)).
        iApply lift_step. auto_STLCmuVS_step. iEval (simplify_custom).
        rewrite !val_subst_valid.
        (* applying IHτ1 *)
        iApply (lift_bind  _ _ _ [AppRCtx _ ; AppRCtx _] [AppRCtx _ ; AppRCtx _]).
        iSplitL.
        iApply (IHτ1 with "H"); auto.
        (* *)
        iIntros (x x') "#Hxx'/=".
        (* using IHτ2 *)
        iApply (lift_bind  _ _ _ [AppRCtx _] [AppRCtx _]).
        iSplitL. iApply "Hvv'". auto.
        iIntros (y y') "#Hyy'".  iEval simpl.
        iApply (IHτ2 with "H").
        by iApply "Hyy'".
      + iIntros (v v') "#Hvv'".
        (* step impl spec *)
        iEval (repeat rewrite -val_subst_valid).
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom. rewrite extract_Closed.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        (* val relation *)
        repeat assert (∀ e, Lam e = of_val $ LamV e) as ->; auto. iApply lift_val.
        iEval rewrite valrel_typed_TArrow_unfold. repeat iModIntro.
        iIntros (w w') "#Hww'".
        (* step impl spec *)
        iEval (repeat rewrite val_subst_valid).
        iApply lift_step. auto_STLCmuVS_step.
        iEval simplify_custom.
        iEval (repeat rewrite -val_subst_valid). iEval asimpl.
        iApply lift_step_later. auto_STLCmuVS_step. simpl. rewrite to_of_val. simpl. asimpl.
        rewrite extract_Closed.
        repeat rewrite val_subst_valid.
        iApply (bind_lift_extract [AppLCtx _ ; AppRCtx _] [AppLCtx _ ; AppRCtx _ ] _ _ _). iNext.
        iSplitL. by iApply lift_val. iNext.
        iIntros (f f') "#Hff".
        iDestruct "Hff" as (e) "(%eq & #Hff)". iEval simpl.
        iApply (lift_bind _ _ _ [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _]). iSplitL. iApply IHτ1; auto.
        iIntros (x x') "#Hxx". iEval simpl. rewrite eq.
        (iApply lift_step_later; first auto_STLCmuVS_step); iEval simplify_custom. iNext.
        iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _]). iSplitL. iApply "Hff"; auto.
        iIntros (y y') "Hyy". simpl. iApply IHτ2;  auto.
    - assert (p : Closed_n (length (TRec τb.[up (subst_list τs)] :: τs)) τb) by closed_solver.
      specialize (IHτb (TRec τb.[up (subst_list τs)] :: τs) p). clear p.
      iIntros "#H".
      iLöb as "IHLob".
      iSplit.
      + iIntros (v v') "#Hvv'". iEval simpl. rewrite valrel_typed_TRec_unfold.
        iDestruct "Hvv'" as (w w') "(-> & -> & #Hww')".
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iEval (rewrite FixArrow_subst).
        iEval (rewrite FixArrow_subst).
        iApply lift_nsteps_later. apply (nsteps_STLCmuVS_step_ctx (fill [AppLCtx _; FstCtx ; AppLCtx _])).
        apply FixArrow_eval.
        iApply lift_rtc_steps. eapply rtc_nsteps_2. apply (nsteps_STLCmuVS_step_ctx (fill [AppLCtx _; FstCtx ; AppLCtx _])).
        apply FixArrow_eval.
        repeat iNext. iEval simplify_custom.
        repeat iEval (rewrite FixArrow_subst !val_subst_valid !val_subst_comp).
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom. rewrite inject_Closed extract_Closed.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom. rewrite inject_Closed.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        repeat iEval (rewrite !val_subst_valid !val_subst_comp). iEval asimpl.
        iApply lift_step_later. auto_STLCmuVS_step. simpl. rewrite !to_of_val. simplify_option_eq.
        iApply lift_step. auto_STLCmuVS_step. simpl. rewrite !to_of_val. simplify_option_eq.
        iEval (change (Lam ?e) with (of_val $ LamV e)). repeat rewrite subst_list_val_cons. repeat iNext.
        iApply (lift_bind _ _  _ [FoldCtx; AppRCtx _] [FoldCtx]).
        iSplitL. iApply IHτb; [| by asimpl]. simpl.
        iModIntro. iFrame "H".
        { repeat rewrite /= /eg_Connective !FixArrow_subst -!val_subst_valid. by asimpl. }
        iIntros (x x') "#Hxx". simpl. change (Fold (of_val ?v)) with (of_val (FoldV v)).
        iApply lift_step_later. apply inject_step'. iApply lift_val. iNext.
        iEval (rewrite valrel_unfold). iExists TCRec. iExists _. iSplit; eauto. repeat iExists _. iSplit; auto.
      + iIntros (v v') "#Hvv'". iEval simpl.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        repeat iEval (rewrite FixArrow_subst).
        iApply lift_nsteps_later. apply (nsteps_STLCmuVS_step_ctx (fill [AppLCtx _; SndCtx ; AppLCtx _])).
        apply FixArrow_eval. repeat iNext.
        iApply lift_rtc_steps. eapply rtc_nsteps_2. apply (nsteps_STLCmuVS_step_ctx (fill [AppLCtx _; SndCtx ; AppLCtx _])). apply FixArrow_eval.
        repeat iNext. iEval simplify_custom.
        repeat iEval (rewrite FixArrow_subst !val_subst_valid !val_subst_comp).
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        rewrite inject_Closed extract_Closed.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom. rewrite extract_Closed.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        repeat iEval (rewrite !val_subst_valid !val_subst_comp). iEval asimpl.
        iApply (bind_lift_extract (rev [FoldCtx ; AppRCtx _ ; UnfoldCtx]) (rev [FoldCtx ; AppRCtx _ ; UnfoldCtx])). iSplitL. by iApply lift_val. repeat iNext.
        iEval simpl. iIntros (x x') "Hdes". iDestruct "Hdes" as (w w') "(-> & -> & #Hww')".
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom. iNext.
        iApply lift_step. auto_STLCmuVS_step. iEval simplify_custom.
        iEval (change (Lam ?e) with (of_val $ LamV e)). repeat rewrite subst_list_val_cons.
        iApply (lift_bind'' _ [FoldCtx] [FoldCtx]). iApply IHτb; auto. iFrame "H".
        { repeat rewrite /= /eg_Connective !FixArrow_subst -!val_subst_valid. by asimpl. }
        iIntros (x x') "#Hxx". simpl. change (Fold (of_val ?v)) with (of_val (FoldV v)).
        iApply lift_val. rewrite valrel_typed_TRec_unfold. iExists _, _. repeat iSplit; eauto. by asimpl.
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
  Qed.

  Lemma embed_guard_connective (τ : type) (pCτ : Closed τ) (v v' : val) :
    valrel_typed τ v v' ⊢ exprel (ep_pair Embed τ v) (ga_pair Guard τ v') .
  Proof.
    cut (valrel_typed τ.[subst_list []] v v' ⊢ exprel ((ep_pair Embed τ.[subst_list []]).{subst_list_val [] } v)
                                                 ((ga_pair Guard τ.[subst_list []]).{subst_list_val [] } v')
        ).
    rewrite pCτ. asimpl. destruct τ; by asimpl.
    iDestruct (connective_ep_ga τ [] pCτ [] []) as "HHH/=".
    rewrite /eg_Connective. asimpl. iIntros "Hee'". iApply "HHH"; auto.
  Qed.

  Lemma project_assert_connective (τ : type) (pCτ : Closed τ) (v v' : val) :
    valrel v v' ⊢ exprel_typed τ (ep_pair Project τ v) (ga_pair Assert τ v').
  Proof.
     cut (valrel v v' ⊢ exprel_typed τ.[subst_list []] ((ep_pair Project τ.[subst_list []]).{subst_list_val [] } v)
                                         ((ga_pair Assert τ.[subst_list []]).{subst_list_val [] } v')
         ).
    rewrite pCτ. asimpl. destruct τ; by asimpl.
    iDestruct (connective_ep_ga τ [] pCτ [] []) as "HHH/=".
    rewrite /pa_Connective. asimpl. iIntros "Hee'". iApply "HHH"; auto.
  Qed.

  Lemma embed_guard_connective_expr (τ : type) (pCτ : Closed τ) (e e' : expr) :
    exprel_typed τ e e' ⊢ exprel (ep_pair Embed τ e) (ga_pair Guard τ e').
  Proof.
    iIntros "Hee'".
    iApply (lift_bind'' _ [AppRCtx _] [AppRCtx _] with "Hee'").
    iIntros (v v') "#Hvv'". by iApply embed_guard_connective.
  Qed.

  Lemma project_assert_connective_expr (τ : type) (pCτ : Closed τ) (e e' : expr) :
    exprel e e' ⊢ exprel_typed τ (ep_pair Project τ e) (ga_pair Assert τ e').
  Proof.
    iIntros "Hee'".
    iApply (lift_bind'' _ [AppRCtx _] [AppRCtx _] with "Hee'").
    iIntros (v v') "#Hvv'". by iApply project_assert_connective.
  Qed.

End connective_un_le_syn.
