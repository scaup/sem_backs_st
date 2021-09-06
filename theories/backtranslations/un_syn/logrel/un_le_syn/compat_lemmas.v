From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.STLCmuVS Require Import lang wkpre generic.lift reducibility tactics virt_steps.
From st.STLCmu Require Import types.
From st.backtranslations.un_syn Require Import logrel.definitions expressions universe.base universe.paths.

(* uninteresting tactic *)
Ltac stuck_cases tc :=
  destruct tc; ((by contradiction) || (iDestruct "Hvv'" as "[-> ->]"; iApply wp_stuck; head_stuck_solver; fail "hmm") ||
        (by iDestruct "HHH" as "[-> ->]"; iApply wp_stuck; head_stuck_solver) ||
        (by iDestruct "HHH" as (b) "[-> ->]"; iApply wp_stuck; head_stuck_solver) ||
        (by iDestruct "HHH" as (z) "[-> ->]"; iApply wp_stuck; head_stuck_solver) ||
        (by iDestruct "HHH" as (a1 a2 a1' a2') "(-> & -> & _ & _)"; iApply wp_stuck; head_stuck_solver) ||
        (by iDestruct "HHH" as (vi vi') "[(-> & -> & _) | (-> & -> & _)]"; iApply wp_stuck; head_stuck_solver) ||
        (by iDestruct "HHH" as (z) "(-> & _)"; iApply wp_stuck; head_stuck_solver) ||
        (by iDestruct "HHH" as (z z') "(-> & -> & _)"; iApply wp_stuck; head_stuck_solver) ||
        (by iDestruct "HHH" as (z z') "(-> & -> & _)"; iApply wp_stuck; head_stuck_solver)).

Section un_le_syn.

  Instance rfn : refinement := un_le_syn.

  Context `{Σ : !gFunctors}.
  Context `{irisGS_inst : !irisGS STLCmuVS_lang Σ}.

  (* Partial map, mapping destructor (one-level) evaluation contexts to the corresponding type constructor. *)
  Definition ectx_item_tc (Ki : ectx_item) : option type_constructor :=
    match Ki with
    | LetInCtx e2 => None
    | AppLCtx e2 => Some TCArrow
    | AppRCtx v1 => None
    | PairLCtx e2 => None
    | PairRCtx v1 => None
    | FstCtx => Some TCProd
    | SndCtx => Some TCProd
    | InjLCtx => None
    | InjRCtx => None
    | CaseCtx e1 e2 => Some TCSum
    | IfCtx e2 e3 => Some TCBool
    | BinOpLCtx op e2 => Some TCInt
    | BinOpRCtx op v1 => Some TCInt
    | SeqCtx e2 => Some TCUnit
    | FoldCtx => None
    | UnfoldCtx => Some TCRec
    | StepCtx => None
    end.


  (* this is where the heavy lifting happens *)
  Lemma ectx_item_extract_val Φ (Kiᵢ : ectx_item) (Kᵢ Kₛ : list ectx_item) tc (H : ectx_item_tc Kiᵢ = Some tc) (v u : val) :
    (valrel v u ∗ ∀ wᵢ wₛ, canon_tc_lift tc valrel wᵢ wₛ -∗ lift? Φ (fill Kᵢ $ fill_item Kiᵢ wᵢ) (fill Kₛ wₛ))
    ⊢ lift? Φ (fill Kᵢ $ fill_item Kiᵢ v) (fill Kₛ $ extract tc u).
  Proof.
    destruct Kiᵢ; rewrite /ectx_item_tc in H;
      ((by inversion H) ||
       (inversion H as [eq]); simplify_eq; iIntros "[#Hv'u H]"; iEval (simpl); iEval (rewrite valrel_unfold /=) in "Hv'u"; iDestruct "Hv'u" as (tc v') "[-> HHH]").
    - destruct (decide (tc = TCArrow)) as [-> | bb].
      + iApply lift_rtc_steps. apply (rtc_STLCmuVS_step_ctx (fill Kₛ)). eapply rtc_l. apply extract_step. apply eval_same_tc. by iApply "H".
      + iApply (wp_bind (fill (AppRCtx _ :: Kᵢ))). iApply wp_wand. iApply wp_Maybestuck_True. iIntros (w _). simpl.
        iApply (wp_bind (fill Kᵢ)). stuck_cases tc.
    - destruct (decide (tc = TCProd)) as [-> | bb].
      + iApply lift_rtc_steps. apply (rtc_STLCmuVS_step_ctx (fill Kₛ)). eapply rtc_l. apply extract_step. apply eval_same_tc. by iApply "H".
      + iApply (wp_bind (fill Kᵢ)). stuck_cases tc.
    - destruct (decide (tc = TCProd)) as [-> | bb].
      + iApply lift_rtc_steps. apply (rtc_STLCmuVS_step_ctx (fill Kₛ)). eapply rtc_l. apply extract_step. apply eval_same_tc. by iApply "H".
      + iApply (wp_bind (fill Kᵢ)). stuck_cases tc.
    - destruct (decide (tc = TCSum)) as [-> | bb].
      + iApply lift_rtc_steps. apply (rtc_STLCmuVS_step_ctx (fill Kₛ)). eapply rtc_l. apply extract_step. apply eval_same_tc. by iApply "H".
      + iApply (wp_bind (fill Kᵢ)). stuck_cases tc.
    - destruct (decide (tc = TCBool)) as [-> | bb].
      + iApply lift_rtc_steps. apply (rtc_STLCmuVS_step_ctx (fill Kₛ)). eapply rtc_l. apply extract_step. apply eval_same_tc. by iApply "H".
      + iApply (wp_bind (fill Kᵢ)). stuck_cases tc.
    - destruct (decide (tc = TCInt)) as [-> | bb].
      + iApply lift_rtc_steps. apply (rtc_STLCmuVS_step_ctx (fill Kₛ)). eapply rtc_l. apply extract_step. apply eval_same_tc. by iApply "H".
      + iApply (wp_bind (fill (BinOpRCtx _ _ :: Kᵢ))). iApply wp_wand. iApply wp_Maybestuck_True. iIntros (w _). simpl. iApply (wp_bind (fill Kᵢ)). stuck_cases tc.
    - destruct (decide (tc = TCInt)) as [-> | bb].
      + iApply lift_rtc_steps. apply (rtc_STLCmuVS_step_ctx (fill Kₛ)). eapply rtc_l. apply extract_step. apply eval_same_tc. by iApply "H".
      + iApply (wp_bind (fill Kᵢ)). stuck_cases tc.
    - destruct (decide (tc = TCUnit)) as [-> | bb].
      + iApply lift_rtc_steps. apply (rtc_STLCmuVS_step_ctx (fill Kₛ)). eapply rtc_l. apply extract_step. apply eval_same_tc. by iApply "H".
      + iApply (wp_bind (fill Kᵢ)). stuck_cases tc.
    - destruct (decide (tc = TCRec)) as [-> | bb].
      + iApply lift_rtc_steps. apply (rtc_STLCmuVS_step_ctx (fill Kₛ)). eapply rtc_l. apply extract_step. apply eval_same_tc. by iApply "H".
      + iApply (wp_bind (fill Kᵢ)). stuck_cases tc.
  Qed.

  Lemma ectx_item_extract_bind Φ (Kiᵢ : ectx_item) (Kᵢ Kₛ : list ectx_item) tc (H : ectx_item_tc Kiᵢ = Some tc) (eᵢ eₛ : expr) :
    (exprel eᵢ eₛ ∗ ∀ vᵢ vₛ, canon_tc_lift tc valrel vᵢ vₛ -∗ lift? Φ (fill Kᵢ (fill_item Kiᵢ vᵢ)) (fill Kₛ vₛ))
    ⊢ lift? Φ (fill Kᵢ (fill_item Kiᵢ eᵢ)) (fill Kₛ (extract tc eₛ)).
  Proof.
    iIntros "[Hee' H]". iApply (lift_bind MaybeStuck _ _ (Kiᵢ :: Kᵢ) (AppRCtx _ :: Kₛ)).
    iSplitL "Hee'". auto. iIntros (v u) "#Hvu". simpl.
    iApply (ectx_item_extract_val); auto.
  Qed.

  Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
  Hint Extern 10 (IntoVal _ _) =>
    rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

  Context (n : nat).

  Lemma compat_Var:
    ∀ x : nat, x < n → open_exprel n (%x)%Eₙₒ (%x)%Eₙₒ .
  Proof.
    intros x H. iIntros (vs vs' Hlvs) "#Hvv's".
    destruct (Var_subst_list_closed_n_length vs x) as [v [eqv ->]]. apply ids_lt_Closed_n. by rewrite Hlvs.
    iDestruct (big_sepL2_length with "Hvv's") as %Hl.
    destruct (Var_subst_list_closed_n_length vs' x) as [v' [eqv' ->]]. apply ids_lt_Closed_n. by rewrite -Hl Hlvs.
    rewrite /exprel /=. iApply lift_val.
    iApply ((big_sepL2_lookup _ vs vs' x _ _ eqv eqv') with "Hvv's").
  Qed.

  Lemma compat_LetIn :
    ∀ e1 e1' e2 e2' : expr, open_exprel n e1 e1' → open_exprel (S n) e2 e2' →
                                            open_exprel n (LetIn e1 e2) (LetIn e1' e2').
  Proof.
    intros e1 e1' e2 e2' IH1 IH2.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    iApply (lift_bind _ _ _ [LetInCtx _] [LetInCtx _]). iSplitL "". iApply IH1; auto.
    iIntros (u v') "Huv'/=". iApply lift_step_later. asimpl. auto_STLCmuVS_step. iApply lift_step. auto_STLCmuVS_step. iNext. simplify_custom. asimpl. do 2 rewrite subst_list_val_cons.
    iApply IH2; auto. simpl. auto.
  Qed.

  Lemma compat_Lam:
    ∀ e e' : expr, open_exprel (S n) e e' → open_exprel n (Lam e) (inject TCArrow (Lam e')).
  Proof.
    intros e e' IH.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= inject_Closed.
    iApply lift_step. eapply (inject_step _ _ (LamV _)). auto.
    change (Lam ?e) with (of_val $ LamV e). iApply lift_val.
    rewrite valrel_unfold. iExists TCArrow. fold valrel. iExists (LamV e'.[up (subst_list_val vs')]). iSplit; auto.
    simpl. iExists _. repeat iSplit; auto.
    do 2 iModIntro. iIntros (w w') "#Hww'".
    iApply lift_step. auto_STLCmuVS_step.
    simplify_custom. asimpl. do 2 rewrite subst_list_val_cons.
    iApply IH. by simpl. simpl. auto.
  Qed.

  Lemma compat_App:
    ∀ e1 e1' e2 e2' : expr,
      open_exprel n e1 e1' → open_exprel n e2 e2' → open_exprel n (e1 e2) (extract TCArrow e1' e2').
  Proof.
    intros e1 e1' e2 e2' IH1 IH2.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite extract_Closed.
    iApply (ectx_item_extract_bind _ (AppLCtx _) [] [AppLCtx _]); auto. iSplitL "". iApply IH1; auto.
    iIntros (v v') "des". iDestruct "des" as (e) "(-> & #H)/=".
    change (Lam e) with (of_val $ LamV e).
    (* change (Lam e') with (of_val $ LamV e'). *)
    iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _]). iSplitL "". iApply IH2; auto. simpl.
    iIntros (u w') "#Huw'/=". iApply lift_step_later. auto_STLCmuVS_step. simplify_custom.
    iNext. by iApply "H".
  Qed.

  Lemma compat_Lit: ∀ l : base_lit, open_exprel n l
                                                match l with
                                                | LitInt n0 => inject TCInt n0
                                                | LitBool b => inject TCBool b
                                                | LitUnit => inject TCUnit ()%Eₙₒ
                                                end.
  Proof.
    intro l. iIntros (vs vs' Hlvs) "#Hvv's".
    destruct l; asimpl; rewrite inject_Closed.
    + iApply lift_step. eapply (inject_step _ _ n0); auto. change (Lit n0) with (of_val n0). iApply lift_val.
      rewrite valrel_unfold. iExists TCInt. iExists _. iSplit; auto. simpl. iExists n0 ; (iSplit; eauto).
    + iApply lift_step. eapply (inject_step _ _ b); auto. change (Lit b) with (of_val b). iApply lift_val.
      rewrite valrel_unfold. iExists TCBool. iExists _; iSplit; auto. simpl. iExists _ ; (iSplit; eauto).
    + iApply lift_step. eapply (inject_step _ _ ()%Vₙₒ); auto. change ()%Eₙₒ with (of_val ()%Vₙₒ). iApply lift_val.
      rewrite valrel_unfold. iExists TCUnit. iExists _; iSplit; auto.
  Qed.

  Lemma compat_BinOp: ∀ (op : bin_op) (e1 e1' e2 e2' : expr),
      open_exprel n e1 e1' → open_exprel n e2 e2'
      → open_exprel n (BinOp op e1 e2)
                    (inject match op with
                            | PlusOp | MinusOp => TCInt
                            | _ => TCBool
                            end (BinOp op (extract TCInt e1') (extract TCInt e2'))).
  Proof.
    intros op e1 e1' e2 e2' IH1 IH2.
    iIntros (vs vs' Hlvs) "#Hvv's".
    rewrite /= extract_Closed. rewrite inject_Closed.
    iApply (lift_bind _ (λne v v', canon_tc_lift (match op with PlusOp | MinusOp => TCInt | _ => TCBool end) valrel v v') _ [] [AppRCtx _]). iSplitL "".
    (* iApply (lift_bind _ (λne v v', canon_tc_lift (match op with PlusOp | MinusOp => TCInt | _ => TCBool end) valrel v v') _ [AppRCtx _] []). iSplitL "". *)
    iApply (ectx_item_extract_bind _ (BinOpLCtx _ _) [] [BinOpLCtx _ _]); auto. iSplitL "". iApply IH1; auto. iIntros (v v') "#Hvv'".
    iApply (ectx_item_extract_bind _ (BinOpRCtx _ _) [] [BinOpRCtx _ _]); auto. iSplitL "". iApply IH2; auto. iIntros (w w') "#Hww'".
    iDestruct "Hvv'" as (a) "[-> ->]". iDestruct "Hww'" as (b) "[-> ->]".
    iApply lift_step_later. auto_STLCmuVS_step. iNext. iApply lift_step. auto_STLCmuVS_step. simpl. iApply lift_val. simpl. destruct op; iExists _; iSplit; auto.
    iIntros (v v') "Hvv'". simpl. iApply lift_step. apply inject_step'. iApply lift_val. rewrite valrel_unfold; iExists _; iExists _. iSplitR. auto. auto.
  Qed.

  Lemma compat_If:
    ∀ e0 e0' e1 e1' e2 e2' : expr,
         open_exprel n e0 e0'
         → open_exprel n e1 e1'
         → open_exprel n e2 e2' → open_exprel n (If e0 e1 e2) (If (extract TCBool e0') e1' e2').
  Proof.
    intros e0 e0' e1 e1' e2 e2' IHe1 IHe2 IHe3.
    iIntros (vs vs' Hlvs) "#Hvv's".
    (* if *) rewrite /= extract_Closed.
    iApply (ectx_item_extract_bind _ (IfCtx _ _) [] [IfCtx _ _]); auto. iSplitL "". iApply IHe1; auto.
    iIntros (v v') "Hvv'". simpl. iDestruct "Hvv'" as (b) "[-> ->]". destruct b.
    + iApply lift_step_later. auto_STLCmuVS_step. iNext. iApply lift_step. auto_STLCmuVS_step. simpl. iApply IHe2; auto.
    + iApply lift_step_later. auto_STLCmuVS_step. iNext. iApply lift_step. auto_STLCmuVS_step. simpl. iApply IHe3; auto.
  Qed.

  Lemma compat_Seq:
    ∀ e1 e1' e2 e2' : expr,
      open_exprel n e1 e1'
      → open_exprel n e2 e2' → open_exprel n (Seq e1 e2) (Seq (extract TCUnit e1') e2').
  Proof.
    intros e1 e1' e2 e2' IHe1 IHe2.
    iIntros (vs vs' Hlvs) "#Hvv's".
    rewrite /= extract_Closed.
    iApply (ectx_item_extract_bind _ (SeqCtx _) [] [SeqCtx _]); auto. iSplitL "". iApply IHe1; auto.
    iIntros (v v') "[-> ->]". simpl.
    iApply lift_step. auto_STLCmuVS_step. simpl. iApply lift_step_later. auto_STLCmuVS_step. simpl.
    iApply IHe2; auto.
  Qed.

  Lemma compat_Pair:
    ∀ e1 e1' e2 e2' : expr,
      open_exprel n e1 e1'
      → open_exprel n e2 e2' → open_exprel n (e1, e2)%Eₙₒ (inject TCProd (e1', e2')%Eₙₒ).
  Proof.
    intros e1 e1' e2 e2' IHe1 IHe2.
    iIntros (vs vs' Hlvs) "#Hvv's".
    asimpl. rewrite inject_Closed.
      iApply (lift_bind _ _ _ [PairLCtx _] [PairLCtx _; AppRCtx _]). iSplitL "". iApply IHe1; auto. iIntros (u1 v1') "#IHu1v1'". simpl.
      iApply (lift_bind _ _ _ [PairRCtx _] [PairRCtx _; AppRCtx _]). iSplitL "". iApply IHe2; auto. iIntros (u2 v2') "#IHu2v2'". simpl.
      iApply lift_step. apply inject_step with (v := PairV v1' v2'); eauto.
      change (u1,u2)%Eₙₒ with (of_val (u1,u2)%Vₙₒ). iApply lift_val.
      iEval (rewrite valrel_unfold). iExists TCProd. iExists _. iSplit; auto. iExists _, _, _, _. repeat iSplit; done.
  Qed.

  Lemma compat_Fst:
    ∀ e e' : expr, open_exprel n e e' → open_exprel n (Fst e) (Fst (extract TCProd e')).
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's".
    asimpl. rewrite extract_Closed.
    iApply (ectx_item_extract_bind _ FstCtx [] [FstCtx]); auto. iSplitL "". iApply IHe; auto.
    iIntros (v v') "Hvv'". simpl. iDestruct "Hvv'" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
    iApply lift_step_later. auto_STLCmuVS_step. iNext. iApply lift_step. auto_STLCmuVS_step. simplify_custom. by iApply lift_val.
  Qed.

  Lemma compat_Snd:
    ∀ e e' : expr, open_exprel n e e' → open_exprel n (Snd e) (Snd (extract TCProd e')).
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's".
    asimpl. rewrite extract_Closed.
    iApply (ectx_item_extract_bind _ SndCtx [] [SndCtx]); auto. iSplitL "". iApply IHe; auto.
    iIntros (v v') "Hvv'". simpl. iDestruct "Hvv'" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
    iApply lift_step_later. auto_STLCmuVS_step. iNext. iApply lift_step. auto_STLCmuVS_step. simplify_custom. by iApply lift_val.
  Qed.

  Lemma compat_InjL:
    ∀ e e' : expr, open_exprel n e e' → open_exprel n (InjL e) (inject TCSum (InjL e')).
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's".
    rewrite /= inject_Closed.
    iApply (lift_bind _ _ _ [InjLCtx] [InjLCtx; AppRCtx _] ). iSplitL "". iApply IHe; auto.
    iIntros (u' v) "#Hvu'". simpl.
    iApply lift_step. apply inject_step with (v := InjLV v). auto. change (InjL u') with (of_val (InjLV u')).
    iApply lift_val. iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; auto. iExists _, _. repeat iSplit; auto.
  Qed.

  Lemma compat_InjR:
    ∀ e e' : expr, open_exprel n e e' → open_exprel n (InjR e) (inject TCSum (InjR e')).
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's".
    rewrite /= inject_Closed.
    iApply (lift_bind _ _ _ [InjRCtx] [InjRCtx; AppRCtx _]). iSplitL "". iApply IHe; auto.
    iIntros (u' v) "#Hvu'". simpl.
    iApply lift_step. apply inject_step with (v := InjRV v). auto. change (InjR u') with (of_val (InjRV u')).
    iApply lift_val. iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; auto. iExists _, _. repeat iSplit; auto.
  Qed.

  Lemma compat_Case:
    ∀ e0 e0' e1 e1' e2 e2' : expr,
         open_exprel n e0 e0'
         → open_exprel (S n) e1 e1'
         → open_exprel (S n) e2 e2'
         → open_exprel n (Case e0 e1 e2) (Case (extract TCSum e0') e1' e2').
  Proof.
    intros e0 e0' e1 e1' e2 e2' IHe0 IHe1 IHe2.
    iIntros (vs vs' Hlvs) "#Hvv's".
    rewrite /= extract_Closed.
    iApply (ectx_item_extract_bind _ (CaseCtx _ _) [] [CaseCtx _ _]); auto. iSplitL "". iApply IHe0; auto.
    iIntros (v v') "Hvv'". simpl. iDestruct "Hvv'" as (vi vi') "[(-> & -> & #H1) | (-> & -> & #H2)]".
    + iApply lift_step_later. auto_STLCmuVS_step. iNext. iApply lift_step. auto_STLCmuVS_step. simplify_custom. asimpl. do 2 rewrite subst_list_val_cons. iApply IHe1; auto. simpl. auto.
    + iApply lift_step_later. auto_STLCmuVS_step. iNext. iApply lift_step. auto_STLCmuVS_step. simplify_custom. asimpl. do 2 rewrite subst_list_val_cons. iApply IHe2; auto. simpl. auto.
  Qed.

  Lemma compat_Fold:
    ∀ e e' : expr, open_exprel n e e' → open_exprel n (Fold e) (inject TCRec (Fold e')).
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's".
    rewrite /= inject_Closed.
    iApply (lift_bind _ _ _ [FoldCtx] [FoldCtx; AppRCtx _]). iSplitL "". iApply IHe; auto.
    iIntros (u' v) "#Hvu'". simpl. iApply lift_step. apply inject_step with (v := FoldV v); auto. change (Fold u') with (of_val $ FoldV u').
    iApply lift_val. iEval (rewrite valrel_unfold). iExists TCRec. iExists _. iSplit; auto. iExists _, _. repeat iSplit; auto.
  Qed.

  Lemma compat_Unfold:
    ∀ e e' : expr, open_exprel n e e' → open_exprel n (Unfold e) (Unfold (extract TCRec e')).
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's".
    rewrite /= extract_Closed.
    iApply (ectx_item_extract_bind _ UnfoldCtx [] [UnfoldCtx]); auto. iSplitL "". iApply IHe; auto.
    iIntros (v v') "Hvv'". simpl. iDestruct "Hvv'" as (w w') "(-> & -> & #H)".
    iApply lift_step_later. auto_STLCmuVS_step. iNext. iApply lift_step. auto_STLCmuVS_step. simplify_custom. by iApply lift_val.
  Qed.


  Lemma compat_VirtStep_help : ∀ v v',
      valrel v v' ⊢ valrel (VirtStepped v) v'.
  Proof.
    iLöb as "IHlob".
    iIntros (v v') "#Hvv'".
    iEval (rewrite valrel_unfold) in "Hvv'". fold valrel. iDestruct "Hvv'" as (tc w) "[-> Hcan]".
    destruct tc; iEval (simpl) in "Hcan".
    - iDestruct "Hcan" as "[-> ->]". simpl.
      rewrite valrel_unfold. iExists TCUnit, _. auto.
    - iDestruct "Hcan" as (b) "[-> ->]". simpl.
      rewrite valrel_unfold. iExists TCBool, _. iSplit; auto. by iExists _.
    - iDestruct "Hcan" as (z) "[-> ->]". simpl.
      rewrite valrel_unfold. iExists TCInt, _. iSplit; auto. by iExists _.
    - iDestruct "Hcan" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)". simpl.
      iEval (rewrite valrel_unfold). fold valrel. iExists TCProd, _. iSplit; auto.
      iExists _, _, _, _. repeat iSplit; eauto; by iApply "IHlob".
    - iDestruct "Hcan" as (vi vi') "[(-> & -> & #H) | (-> & -> & #H)]/=";
        iEval (rewrite valrel_unfold); fold valrel; iExists TCSum;
          iExists _; iSplit; auto; repeat iExists _.
      + iLeft. repeat iSplit; eauto. by iApply "IHlob".
      + iRight. repeat iSplit; eauto. by iApply "IHlob".
    - rename w into x. iDestruct "Hcan" as (e) "[-> #H]";
        iEval (rewrite valrel_unfold); fold valrel; iExists TCArrow.
      iExists _; iSplit; eauto. simpl. iExists _. iSplit; eauto. iNext.
      iDestruct "H" as "#H". iModIntro.
      iIntros (w w') "Hww'".
      iAssert (valrel (VirtStepped w) w') with "[Hww']" as "Hwws'". by iApply "IHlob".
      iSpecialize ("H" $! (VirtStepped w) w' with "Hwws'").
      asimpl. change (Lam e) with (of_val (LamV e)). iApply lift_rtc_steps_impl.
      eapply rtc_transitive.
      apply (rtc_STLCmuVS_step_ctx (fill [AppRCtx _; VirtStepCtx])). apply VirtStep_eval. simpl.
      change (Lam e) with (of_val (LamV e)).
      apply (rtc_STLCmuVS_step_ctx (fill [VirtStepCtx])).
      eapply rtc_once. auto_STLCmuVS_step. simplify_custom.
      iApply (lift_bind _ _ _ [VirtStepCtx] []). iFrame "H".
      iIntros (v v') "#Hvv'". iApply lift_rtc_steps_impl. apply VirtStep_eval.
      iApply lift_val. by iApply "IHlob".
    - iDestruct "Hcan" as (x x') "(-> & -> & #H)";
        iEval (rewrite valrel_unfold); fold valrel; iExists TCRec.
      iExists _; eauto. iSplit; eauto. iExists _, _. repeat iSplit; eauto. by iApply "IHlob".
  Qed.

  Lemma compat_VirtStep e e' :
    open_exprel n e e' →
    open_exprel n (VirtStep e) e'.
  Proof.
    iIntros (IHe vs vs' Hlvs) "#Hvv's". asimpl.
    iApply (lift_bind _ _ _ [VirtStepCtx] []). iSplitL "". iApply IHe; auto.
    iIntros (v v') "#Hvv'". iClear "Hvv's". simpl.
    iApply lift_rtc_steps_impl. apply VirtStep_eval.
    iApply lift_val. by iApply compat_VirtStep_help.
  Qed.

End un_le_syn.
