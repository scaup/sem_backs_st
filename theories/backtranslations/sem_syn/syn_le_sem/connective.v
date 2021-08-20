From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst.
From st.STLCmuVS Require Import types lang typing tactics logrel.definitions logrel.generic.lift.
From st.STLCmuVS.lib Require Import fixarrow.
From st.backtranslations.un_syn Require Import logrel.definitions universe.base universe.paths logrel.syn_le_un.compat_lemmas.
From st.backtranslations.sem_syn Require Import embed_project.
From st Require Import resources.
(* logrel.un_le_syn.fundamental. *)

(* Defines connective lemma between the untyped and typed logic relations (the (syntactically typed ≤ untyped)-refinement) *)
(* Of the two refinements, this is the easier one *)
Section connective_syn_le_un.

  Instance rfn' : refinement := syn_le_un.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Notation valrel_typed := (valrel_typed MaybeStuck).
  Notation exprel_typed := (exprel_typed MaybeStuck).

  Definition emb_Connective (τ : type) (emb : val) : iProp Σ :=
    ∀ (v v' : val), (valrel_typed τ v v' -∗ exprel (emb v) v').

  Definition prj_Connective (τ : type) (prj : val) : iProp Σ :=
    ∀ (v v' : val), (valrel v v' -∗ exprel_typed τ (prj v) v').

  Lemma connective_ep : ∀ (τ : type) (τs : list type) (pCnτ : Closed_n (length τs) τ) (eps : list val),
    □ ([∗ list] τ ; ep ∈ τs ; eps,
       (emb_Connective τ (LamV (Fst (ep.{ren (+1)} ()) %0)%Eₙₒ) ∧
       prj_Connective τ (LamV (Snd (ep.{ren (+1)} ()) %0)%Eₙₒ))
      ) ⊢ emb_Connective τ.[subst_list τs] (ep_pair Embed τ).{subst_list_val eps} ∧
          prj_Connective τ.[subst_list τs] (ep_pair Project τ).{subst_list_val eps}.
  Proof.
    iLöb as "IHlob".
    iIntros (τ). iInduction τ as [] "IH";
      iIntros (τs pτ eps) "#Hl".
    - iEval (rewrite /emb_Connective /prj_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iIntros (v v') "Hvv". rewrite valrel_typed_TUnit_unfold. iDestruct "Hvv" as "[-> ->]".
        iApply lift_step_later. eapply inject_step'. iApply lift_val.
        rewrite valrel_unfold. iExists TCUnit. by iExists ()%Vₙₒ.
      + iIntros (v v') "Hvv". simpl.
        iApply (bind_lift_extract [] [] v v' TCUnit). iSplitL. by iApply lift_val. iNext.
        iIntros (w w') "[-> ->]". iApply lift_val. by rewrite valrel_typed_TUnit_unfold.
    - iEval (rewrite /emb_Connective /prj_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iIntros (v v') "Hvv". rewrite valrel_typed_TBool_unfold. iDestruct "Hvv" as (b) "[-> ->]".
        iApply lift_step_later. eapply inject_step'. iApply lift_val.
        rewrite valrel_unfold. iExists TCBool. iExists b. repeat iSplit; auto. simpl. by iExists b.
      + iIntros (v v') "Hvv". simpl.
        iApply (bind_lift_extract [] [] v v' TCBool). iSplitL. by iApply lift_val. iNext.
        iIntros (w w') "des". iDestruct "des" as (b) "[-> ->]". iApply lift_val. rewrite valrel_typed_TBool_unfold. by iExists b.
    - iEval (rewrite /emb_Connective /prj_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iIntros (v v') "Hvv". rewrite valrel_typed_TInt_unfold. iDestruct "Hvv" as (i) "[-> ->]".
        iApply lift_step_later. eapply inject_step'. iApply lift_val.
        rewrite valrel_unfold. iExists TCInt. iExists i. repeat iSplit; auto. simpl. by iExists i.
      + iIntros (v v') "Hvv". simpl.
        iApply (bind_lift_extract [] [] v v'). iSplitL. by iApply lift_val. iNext.
        iIntros (w w') "des". iDestruct "des" as (i) "[-> ->]". iApply lift_val. rewrite valrel_typed_TInt_unfold. by iExists i.
    - iEval (rewrite /emb_Connective /prj_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iIntros (v v') "Hvv". rewrite valrel_typed_TProd_unfold.
        iDestruct "Hvv" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
        do 5 ((iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite inject_Closed))).
        do 5 iNext.
        iApply (lift_bind _ _ _ [PairLCtx _; AppRCtx _] [PairLCtx _]). iSplitL.
        rewrite val_subst_valid. iApply "IH"; auto. iPureIntro; closed_solver.
        iIntros (w w') "#Hww". simpl.
        iApply (lift_bind _ _ _ [PairRCtx _; AppRCtx _] [PairRCtx _]). iSplitL.
        rewrite val_subst_valid. iApply "IH1"; auto. iPureIntro; closed_solver.
        iIntros (x x') "#Hxx". simpl.
        change (of_val ?v1, of_val ?v2)%Eₙₒ with (of_val (v1, v2)%Vₙₒ).
        iApply lift_step_later. apply inject_step'. iApply lift_val.
        iEval (rewrite valrel_unfold). iExists TCProd. iExists _. iSplit; eauto. repeat iExists _. iSplit; auto.
      + iIntros (v v') "#Hvv". iEval (simpl).
        (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite !extract_Closed)).
        iApply (bind_lift_extract [LetInCtx _] [] v v'). iSplitL. by iApply lift_val. iNext. iNext.
        iIntros (w w') "des". iDestruct "des" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)". simpl.
        do 5 (iApply lift_step_later; first auto_STLCmuVS_step); iEval simplify_custom. repeat iNext.
        iApply (lift_bind _ _ _ [PairLCtx _] [PairLCtx _]). iSplitL.
        rewrite val_subst_valid. iApply "IH"; auto. iPureIntro; closed_solver.
        iIntros (w w') "#Hww". simpl.
        iApply (lift_bind _ _ _ [PairRCtx _] [PairRCtx _]). iSplitL.
        rewrite val_subst_valid. iApply "IH1"; auto. iPureIntro; closed_solver.
        iIntros (x x') "#Hxx". simpl.
        change (of_val ?v1, of_val ?v2)%Eₙₒ with (of_val (v1, v2)%Vₙₒ). iApply lift_val.
        iEval (rewrite valrel_typed_TProd_unfold). repeat iExists _. iSplit; auto.
    - iEval (rewrite /emb_Connective /prj_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iEval (setoid_rewrite valrel_typed_TSum_unfold).
        iIntros (v v') "Hvv". iDestruct "Hvv" as (vi vi') "[(-> & -> & Hvivi) | (-> & -> & Hvivi)]".
        * iClear "IH1".
          do 2 (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite inject_Closed)). do 2 iNext.
          iApply (lift_bind _ _ _ [InjLCtx; AppRCtx _] [InjLCtx]). iSplitL.
          rewrite val_subst_valid. iApply "IH"; auto. iPureIntro; closed_solver.
          iIntros (v v') "Hvv". simpl. change (InjL (of_val ?v)) with (of_val (InjLV v)).
          iApply lift_step_later. apply inject_step'. iApply lift_val.
          iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; eauto. repeat iExists _. iLeft. iSplit; auto.
        * iClear "IH".
          do 2 (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite inject_Closed)). do 2 iNext.
          iApply (lift_bind _ _ _ [InjRCtx; AppRCtx _] [InjRCtx]). iSplitL.
          rewrite val_subst_valid. iApply "IH1"; auto. iPureIntro; closed_solver.
          iIntros (v v') "Hvv". simpl. change (InjR (of_val ?v)) with (of_val (InjRV v)).
          iApply lift_step_later. apply inject_step'. iApply lift_val.
          iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; eauto. repeat iExists _. iRight. iSplit; auto.
      + iIntros (v v') "Hvv".
        (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        iApply (bind_lift_extract [CaseCtx _ _] [] v v'). iSplitL. by iApply lift_val. iNext.
        iIntros (w w') "des". iDestruct "des" as (vi vi') "[(-> & -> & Hvivi) | (-> & -> & Hvivi)]"; simpl.
        * (iApply lift_step_later; first auto_STLCmuVS_step); iEval simplify_custom. iNext.
          iApply (lift_bind _ _ _ [InjLCtx] [InjLCtx]). iSplitL.
          rewrite val_subst_valid. iApply "IH"; auto. iPureIntro; closed_solver.
          iIntros (w w') "Hww". simpl. change (InjL (of_val ?v)) with (of_val (InjLV v)). iApply lift_val.
          rewrite valrel_typed_TSum_unfold. iExists _, _. iLeft. auto.
        * (iApply lift_step_later; first auto_STLCmuVS_step); iEval simplify_custom. iNext.
          iApply (lift_bind _ _ _ [InjRCtx] [InjRCtx]). iSplitL.
          rewrite val_subst_valid. iApply "IH1"; auto. iPureIntro; closed_solver.
          iIntros (w w') "Hww". simpl. change (InjR (of_val ?v)) with (of_val (InjRV v)). iApply lift_val.
          rewrite valrel_typed_TSum_unfold. iExists _, _. iRight. auto.
    - iEval (rewrite /emb_Connective /prj_Connective /= -!val_subst_valid inject_Closed extract_Closed).
      iSplit.
      + iIntros (v v') "#Hvv". rewrite valrel_typed_TArrow_unfold.
        (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; try rewrite inject_Closed).
        change (Lam ?e) with (of_val $ LamV e).
        iApply lift_step_later. apply inject_step'. iApply lift_val. repeat iNext.
        rewrite valrel_unfold. iExists TCArrow. iExists _. iSplit; auto. simpl.
        iExists _. repeat iSplit; eauto.
        iNext. iModIntro.
        iIntros (w w') "#Hww". asimpl.
        (* iApply (lift_anti_step _ _ _ (v' w')). apply head_prim_step. auto_head_step. *)
        rewrite !val_subst_valid.
        iApply (lift_bind _ _ _ [AppRCtx _; AppRCtx _] [AppRCtx _]). iSplitL.
        iApply "IH"; auto. iPureIntro; closed_solver.
        iIntros (x x') "#Hxx". simpl.
        iApply (lift_bind _ _ _ [AppRCtx _] []). simpl. iSplitL. by iApply "Hvv".
        iIntros (y y') "#Hyy". simpl.
        iApply "IH1"; auto. iPureIntro; closed_solver.
      + iIntros (v v') "#Hvv".
        (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        change (Lam ?e) with (of_val $ LamV e). iApply lift_val.
        rewrite valrel_typed_TArrow_unfold. iModIntro.
        iIntros (w w') "#Hww".
        (iApply lift_step_later; first auto_STLCmuVS_step); iEval (simplify_custom; (try rewrite extract_Closed)). iNext.
        rewrite !val_subst_valid.
        iApply (bind_lift_extract [AppLCtx _ ; AppRCtx _] [AppLCtx _]). iSplitL. by iApply lift_val.
        iNext. iIntros (f f') "#Hff".
        iDestruct "Hff" as (e) "(%eq & #Hff)". iEval simpl.
        iApply (lift_bind _ _ _ [AppRCtx _; AppRCtx _] [AppRCtx _]). iSplitL.
        iApply "IH"; auto. iPureIntro; closed_solver.
        iIntros (x x') "#Hxx". iEval simpl. rewrite eq.
        (iApply lift_step_later; first auto_STLCmuVS_step); iEval simplify_custom. iNext.
        iApply (lift_bind _ _ _ [AppRCtx _] []). iSplitL. by iApply "Hff".
        iIntros (y y') "Hyy". simpl. iApply "IH1"; auto. iPureIntro; closed_solver.
    - assert (p : Closed_n (length (TRec τ.[up (subst_list τs)] :: τs)) τ) by closed_solver.
      iSpecialize ("IH" $! (TRec τ.[up (subst_list τs)] :: τs) p). clear p.
      iSplit.
      + iIntros (v v') "#Hvv'". iEval simpl. rewrite valrel_typed_TRec_unfold.
        iDestruct "Hvv'" as (w w') "(-> & -> & #Hww')".
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iEval (rewrite FixArrow_subst).
        iApply lift_nsteps_later. apply (nsteps_STLCmuVS_step_ctx (fill [AppLCtx _; FstCtx ; AppLCtx _])).
        apply FixArrow_eval. repeat iNext. iEval simplify_custom.
        iEval (rewrite FixArrow_subst !val_subst_valid !val_subst_comp).
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom. rewrite inject_Closed extract_Closed.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom. rewrite inject_Closed.
        iEval (rewrite !val_subst_valid !val_subst_comp). iEval asimpl.
        iApply lift_step_later. auto_STLCmuVS_step. simpl. rewrite !to_of_val. simplify_option_eq.
        iEval (change (Lam ?e) with (of_val $ LamV e)). rewrite subst_list_val_cons. repeat iNext.
        iApply (lift_bind''  _ [FoldCtx; AppRCtx _] [FoldCtx]). iApply "IH"; [|by asimpl]. iFrame "Hl".
        { iClear "IH". iSpecialize ("IHlob" $! (TRec τ) τs pτ eps with "Hl"). iModIntro.
          iSplitL.
          - iDestruct "IHlob" as "[IHlob _]". asimpl. iIntros (v v') "#Hvv'". iSpecialize ("IHlob" $! v v' with "Hvv'").
            simpl. rewrite !FixArrow_subst -!val_subst_valid. by asimpl.
          - iDestruct "IHlob" as "[_ IHlob]". asimpl. iIntros (v v') "#Hvv'". iSpecialize ("IHlob" $! v v' with "Hvv'").
            simpl. rewrite !FixArrow_subst -!val_subst_valid. by asimpl. }
        iIntros (x x') "#Hxx". simpl. change (Fold (of_val ?v)) with (of_val (FoldV v)).
        iApply lift_step_later. apply inject_step'. iApply lift_val. iNext.
        iEval (rewrite valrel_unfold). iExists TCRec. iExists _. iSplit; eauto. repeat iExists _. iSplit; auto.
      + iIntros (v v') "#Hvv'". iEval simpl.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iEval (rewrite FixArrow_subst).
        iApply lift_nsteps_later. apply (nsteps_STLCmuVS_step_ctx (fill [AppLCtx _; SndCtx ; AppLCtx _])).
        apply FixArrow_eval. repeat iNext. iEval simplify_custom.
        iEval (rewrite FixArrow_subst !val_subst_valid !val_subst_comp).
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom. rewrite inject_Closed extract_Closed.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom.
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom. rewrite extract_Closed.
        iEval (rewrite !val_subst_valid !val_subst_comp). iEval asimpl.
        iApply (bind_lift_extract (rev [FoldCtx ; AppRCtx _ ; UnfoldCtx]) []). iSplitL. by iApply lift_val. repeat iNext.
        iEval simpl. iIntros (x x') "Hdes". iDestruct "Hdes" as (w w') "(-> & -> & #Hww')".
        iApply lift_step_later. auto_STLCmuVS_step. iEval simplify_custom. iNext.
        iEval (change (Lam ?e) with (of_val $ LamV e)). rewrite subst_list_val_cons.
        iApply (lift_bind'' _ [FoldCtx] [FoldCtx]). iApply "IH"; auto. iFrame "Hl".
        { iClear "IH". iSpecialize ("IHlob" $! (TRec τ) τs pτ eps with "Hl"). iModIntro.
          iSplitL.
          - iDestruct "IHlob" as "[IHlob _]". asimpl.
            simpl. rewrite !FixArrow_subst -!val_subst_valid. by asimpl.
          - iDestruct "IHlob" as "[_ IHlob]". asimpl.
            simpl. rewrite !FixArrow_subst -!val_subst_valid. by asimpl. }
        iIntros (x x') "#Hxx". simpl. change (Fold (of_val ?v)) with (of_val (FoldV v)).
        iApply lift_val. rewrite valrel_typed_TRec_unfold. iExists _, _. repeat iSplit; eauto. by asimpl.
    - (* TVar *)
      destruct (TVar_subst_list_closed_n_length _ _ pτ) as [τ [eq1 ->]].
      iDestruct (big_sepL2_length with "Hl") as "%H1".
      destruct (eps !! X) as [ep |] eqn:eq2.
      + iDestruct (big_sepL2_lookup _ τs eps X _ _ eq1 eq2 with "Hl") as "[a b]".
        iEval asimpl. change (subst_list_val eps X) with ((ids X).[subst_list_val eps]).
        rewrite (Var_subst_list_val_lookup _ _ _ eq2). rewrite val_subst_valid.
        auto.
      + exfalso.
        assert (length eps ≤ X). by apply lookup_ge_None.
        assert (X < length τs). by eapply lookup_lt_Some. lia.
  Qed.

  Lemma embed_connective (τ : type) (pCτ : Closed τ) (v v' : val) :
    valrel_typed τ v v' ⊢ exprel (ep_pair Embed τ v) v'.
  Proof.
    cut (valrel_typed τ.[subst_list []] v v' ⊢ exprel ((ep_pair Embed τ.[subst_list []]).{subst_list_val [] } v) v').
    rewrite pCτ. asimpl. destruct τ; by asimpl.
    iDestruct (connective_ep τ [] pCτ []) as "HHH/=".
    rewrite /emb_Connective. asimpl. iIntros "Hee'". iApply "HHH"; auto.
  Qed.

  Lemma project_connective (τ : type) (pCτ : Closed τ) (v v' : val) :
    valrel v v' ⊢ exprel_typed τ (ep_pair Project τ v) v'.
  Proof.
     cut (valrel v v' ⊢ exprel_typed τ.[subst_list []] ((ep_pair Project τ.[subst_list []]).{subst_list_val [] } v) v').
     rewrite pCτ. asimpl. destruct τ; by asimpl.
     iDestruct (connective_ep τ [] pCτ []) as "HHH/=".
     rewrite /prj_Connective. asimpl. iIntros "Hee'". iApply "HHH"; auto.
  Qed.

  Lemma project_connective_expr (τ : type) (pCτ : Closed τ) (e e' : expr) :
    exprel e e' ⊢ exprel_typed τ (ep_pair Project τ e) e'.
  Proof.
    iIntros "Hee'".
    iApply (lift_bind'' _ [AppRCtx _] [] with "Hee'").
    iIntros (v v') "#Hvv'". by iApply project_connective.
  Qed.

  Lemma embed_connective_expr (τ : type) (pCτ : Closed τ) (e e' : expr) :
    exprel_typed τ e e' ⊢ exprel (ep_pair Embed τ e) e'.
  Proof.
    iIntros "Hee'".
    iApply (lift_bind'' _ [AppRCtx _] [] with "Hee'").
    iIntros (v v') "#Hvv'". by iApply embed_connective.
  Qed.


End connective_syn_le_un.
