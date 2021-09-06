From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.STLCmuVS Require Import lang virt_steps wkpre generic.lift tactics lib.omega tactics reducibility.
From st.STLCmu Require Import types.
From st.backtranslations.un_syn Require Import logrel.definitions expressions universe.base universe.paths.

Section syn_le_un.

  Instance rfn : refinement := syn_le_un.

  Context `{Σ : !gFunctors}.
  Context `{irisGS_inst : !irisGS STLCmuVS_lang Σ}.

  Lemma wp_Ω Φ : ⊢ WP Ω ?{{Φ}}.
  Proof. iLöb as "IH". iApply wp_nsteps_later. by apply Ω_loop. done. Qed.

  Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
  Hint Extern 10 (IntoVal _ _) =>
    rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.


  Lemma bind_lift_extract (K K' : ectx STLCmuVS_ectx_lang) (e e' : expr) (tc : type_constructor) Φ :
      exprel e e' ∗ (▷ ∀ v v', canon_tc_lift tc valrel v v' -∗ lift? Φ (fill K (of_val v)) (fill K' (of_val v'))) ⊢
        lift? Φ (fill K (extract tc e)) (fill K' e').
  Proof.
    iIntros "[Hee' H]". iApply (lift_bind _ _ _ (AppRCtx _ :: K) K'). iFrame "Hee'".
    iIntros (v u') "#Hvu'". simpl.
    iApply (wp_bind (fill K)). iApply wp_step_later. apply head_prim_step. auto_head_step. iModIntro. asimpl.
    rewrite (valrel_unfold v u').
    iDestruct "Hvu'" as (tc2) "des". iDestruct "des" as (v') "[-> Hvv']".
    rewrite CaseTC_subst. asimpl.
    destruct (decide (tc = tc2)) as [<- | neq] eqn:eq.
    + iApply wp_rtc_steps. apply eval_same_tc.
      iApply wp_value. iApply (wp_wand with "[H]"). iApply "H". auto.
      iIntros (v) "H". auto.
    + iApply wp_rtc_steps. by apply eval_diff_tc.
      iApply wp_Ω.
  Qed.

  Context (n : nat).

  Lemma compat_Var:
    ∀ x : nat, x < n → open_exprel n (%x)%Eₙₒ (%x)%Eₙₒ.
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
    ∀ e e' : expr,
      open_exprel (S n) e e'
      → open_exprel n (inject TCArrow (Lam e)) (Lam e').
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= inject_Closed.
    iApply lift_step_later. eapply (inject_step _ _ (LamV _)). auto. iNext.
    change (Lam ?e) with (of_val $ LamV e). iApply lift_val.
    rewrite valrel_unfold. iExists TCArrow. fold valrel. iExists (LamV e.[up (subst_list_val vs)]). iSplit; auto.
    simpl. iExists _. iSplit. auto.
    do 2 iModIntro. iIntros (w w') "#Hww'".
    iApply lift_step. auto_STLCmuVS_step. simplify_custom.
    asimpl. do 2 rewrite subst_list_val_cons.
    iApply IHe. simpl. lia. simpl. auto.
  Qed.

  Lemma compat_App:
    ∀ e1 e1' e2 e2' : expr,
      open_exprel n e1 e1'
      → open_exprel n e2 e2'
      → open_exprel n (extract TCArrow e1 e2) (e1' e2').
  Proof.
    intros e1 e1' e2 e2' IHe1 IHe2.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    asimpl. rewrite extract_Closed.
    iApply (bind_lift_extract [AppLCtx _] [AppLCtx _]).
    iSplitL "". iApply IHe1; auto. iNext.
    iIntros (v v') "des". simpl. iDestruct "des" as (e) "(-> & #H)".
    iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _]). iSplitL "". iApply IHe2; auto.
    iIntros (w w') "Hww'". simpl. iApply lift_step_later. auto_STLCmuVS_step.
    simplify_custom. iNext. iApply ("H" with "Hww'").
  Qed.

  Lemma compat_Lit:
    ∀ l : base_lit,
      open_exprel n
                  match l with
                  | LitInt n0 => inject TCInt n0
                  | LitBool b => inject TCBool b
                  | LitUnit => inject TCUnit ()%Eₙₒ
                  end l.
  Proof.
    intros l.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /=; destruct l; asimpl; rewrite inject_Closed.
    + iApply lift_step_later. eapply (inject_step _ _ n0); auto. change (Lit n0) with (of_val n0). iApply lift_val.
      rewrite valrel_unfold. iExists TCInt. iExists _. iSplit; auto. simpl. iExists n0 ; (iSplit; eauto).
    + iApply lift_step_later. eapply (inject_step _ _ b); auto. change (Lit b) with (of_val b). iApply lift_val.
      rewrite valrel_unfold. iExists TCBool. iExists _; iSplit; auto. simpl. iExists _ ; (iSplit; eauto).
    + iApply lift_step_later. eapply (inject_step _ _ ()%Vₙₒ); auto. change ()%Eₙₒ with (of_val ()%Vₙₒ). iApply lift_val.
      rewrite valrel_unfold. iExists TCUnit. iExists _; iSplit; auto.
  Qed.

  Lemma compat_BinOp:
    ∀ (op : bin_op) (e1 e1' e2 e2' : expr),
      open_exprel n e1 e1'
      → open_exprel n e2 e2'
      → open_exprel n
                    (inject match op with
                            | PlusOp | MinusOp => TCInt
                            | _ => TCBool
                            end
                            (BinOp op (extract TCInt e1) (extract TCInt e2)))
                    (BinOp op e1' e2').
  Proof.
    intros op e1 e1' e2 e2' IHe1 IHe2.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= inject_Closed extract_Closed.
    iApply (lift_bind' _ _ _ [AppRCtx _; BinOpLCtx _ _; AppRCtx _] [BinOpLCtx _ _]). iApply IHe1. auto. auto.
    iIntros (v1 v1') "#Hv1". simpl.
    iApply (bind_lift_extract [BinOpLCtx _ _; AppRCtx _] [BinOpLCtx _ _]). iSplitL. by iApply lift_val. iNext.
    iIntros (w1 w1') "#Hw1". simpl.
    iApply (lift_bind' _ _ _ [AppRCtx _; BinOpRCtx _ _; AppRCtx _] [BinOpRCtx _ _]). iApply IHe2. auto. auto.
    iIntros (v2 v2') "#Hv2". simpl.
    iApply (bind_lift_extract [BinOpRCtx _ _; AppRCtx _] [BinOpRCtx _ _]). iSplitL. by iApply lift_val. iNext.
    iIntros (w2 w2') "#Hw2". simpl.
    iDestruct "Hw1" as (z1) "[-> ->]".
    iDestruct "Hw2" as (z2) "[-> ->]".
    iApply lift_step_later. auto_STLCmuVS_step.
    iApply lift_step. auto_STLCmuVS_step. simplify_custom.
    iApply lift_step_later. apply inject_step'. iApply lift_val. iNext. iNext.
    iEval (rewrite valrel_unfold).
    destruct op; repeat iExists _; eauto.
  Qed.

  Lemma compat_If:
    ∀ e0 e0' e1 e1' e2 e2' : expr,
      open_exprel n e0 e0'
      → open_exprel n e1 e1'
      → open_exprel n e2 e2'
      → open_exprel n (If (extract TCBool e0) e1 e2)
                    (If e0' e1' e2').
  Proof.
    intros e0 e0' e1 e1' e2 e2' IHe1 IHe2 IHe3.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= extract_Closed.
    iApply (bind_lift_extract [IfCtx _ _] [IfCtx _ _]). iSplitL. iApply IHe1; auto. iNext.
    iIntros (v v') "Hvv". simpl. iDestruct "Hvv" as (b) "[-> ->]".
    destruct b.
    + iApply lift_step_later. auto_STLCmuVS_step. iApply lift_step. auto_STLCmuVS_step. simpl.
      iApply IHe2; auto.
    + iApply lift_step_later. auto_STLCmuVS_step. iApply lift_step. auto_STLCmuVS_step. simpl.
      iApply IHe3; auto.
  Qed.

  Lemma compat_Seq:
    ∀ e1 e1' e2 e2' : expr,
      open_exprel n e1 e1'
      → open_exprel n e2 e2'
      → open_exprel n (Seq (extract TCUnit e1) e2) (Seq e1' e2').
  Proof.
    intros e1 e1' e2 e2' IHe1 IHe2.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= extract_Closed.
    iApply (bind_lift_extract [SeqCtx _] [SeqCtx _]). iSplitL "". iApply IHe1; auto. iNext. simpl.
    iIntros (v v') "[-> ->]". iApply lift_step_later. auto_STLCmuVS_step. iApply lift_step. auto_STLCmuVS_step. simpl.
    iApply IHe2; auto.
  Qed.

  Lemma compat_Pair:
    ∀ e1 e1' e2 e2' : expr,
      open_exprel n e1 e1'
      → open_exprel n e2 e2'
      → open_exprel n (inject TCProd (e1 , e2)%Eₙₒ) (e1', e2')%Eₙₒ.
  Proof.
    intros e1 e1' e2 e2' IHe1 IHe2.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    asimpl. rewrite inject_Closed.
    iApply (lift_bind _ _ _ [PairLCtx _; AppRCtx _] [PairLCtx _]). iSplitL "". iApply IHe1; auto. iIntros (u1 v1') "#IHu1v1'". simpl.
    iApply (lift_bind _ _ _ [PairRCtx _; AppRCtx _] [PairRCtx _]). iSplitL "". iApply IHe2; auto. iIntros (u2 v2') "#IHu2v2'". simpl.
    iApply lift_step_later. apply inject_step with (v := PairV u1 u2); eauto.
    change (v1',v2')%Eₙₒ with (of_val (v1',v2')%Vₙₒ). iApply lift_val.
    iEval (rewrite valrel_unfold). iExists TCProd. iExists _. iSplit; auto. iExists _, _, _, _. repeat iSplit; done.
  Qed.

  Lemma compat_Fst:
    ∀ e e' : expr,
      open_exprel n e e'
      → open_exprel n (Fst (extract TCProd e)) (Fst e').
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= extract_Closed.
    iApply (bind_lift_extract [FstCtx] [FstCtx]). iSplitL "". iApply IHe; auto.
    iNext. iIntros (v v') "des/=". iDestruct "des" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
    iApply lift_step_later. auto_STLCmuVS_step. iApply lift_step. auto_STLCmuVS_step. simplify_custom. iApply lift_val. done.
  Qed.

  Lemma compat_Snd:
    ∀ e e' : expr,
      open_exprel n e e'
      → open_exprel n (Snd (extract TCProd e)) (Snd e').
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= extract_Closed.
    iApply (bind_lift_extract [SndCtx] [SndCtx]). iSplitL "". iApply IHe; auto.
    iNext. iIntros (v v') "des/=". iDestruct "des" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
    iApply lift_step_later. auto_STLCmuVS_step. iApply lift_step. auto_STLCmuVS_step. simplify_custom. iApply lift_val. done.
  Qed.

  Lemma compat_InjL:
    ∀ e e' : expr,
      open_exprel n e e'
      → open_exprel n (inject TCSum (InjL e)) (InjL e').
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= inject_Closed.
    iApply (lift_bind _ _ _ [InjLCtx; AppRCtx _] [InjLCtx]). iSplitL "". iApply IHe; auto.
    iIntros (v u') "#Hvu'". simpl.
    iApply lift_step_later. apply inject_step with (v := InjLV v). auto. iNext. change (InjL u') with (of_val (InjLV u')).
    iApply lift_val. iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; auto. iExists _, _. repeat iSplit; auto.
  Qed.

  Lemma compat_InjR:
    ∀ e e' : expr,
      open_exprel n e e'
      → open_exprel n (inject TCSum (InjR e)) (InjR e').
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= inject_Closed.
    iApply (lift_bind _ _ _ [InjRCtx; AppRCtx _] [InjRCtx]). iSplitL "". iApply IHe; auto.
    iIntros (v u') "#Hvu'". simpl.
    iApply lift_step_later. apply inject_step with (v := InjRV v). auto. iNext. change (InjR u') with (of_val (InjRV u')).
    iApply lift_val. iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; auto. iExists _, _. repeat iSplit; auto.
  Qed.

  Lemma compat_Case:
    ∀ e0 e0' e1 e1' e2 e2' : expr,
      open_exprel n e0 e0'
      → open_exprel (S n) e1 e1'
      → open_exprel (S n) e2 e2'
      → open_exprel n (Case (extract TCSum e0) e1 e2)
                    (Case e0' e1' e2').
  Proof.
    intros e0 e0' e1 e1' e2 e2' IHe0 IHe1 IHe2.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= extract_Closed.
    iApply (bind_lift_extract [CaseCtx _ _] [CaseCtx _ _]). iSplitL "". iApply IHe0; auto.
    iNext. iIntros (v v') "des/=". iDestruct "des" as (vi vi') "[(-> & -> & #Hi)|(-> & -> & #Hi)]".
    + iApply lift_step_later. auto_STLCmuVS_step. iApply lift_step. auto_STLCmuVS_step. simplify_custom. asimpl.
      iNext. do 2 rewrite subst_list_val_cons. iApply IHe1; auto. simpl. auto.
    + iApply lift_step_later. auto_STLCmuVS_step. iApply lift_step. auto_STLCmuVS_step. simplify_custom. asimpl.
      iNext. do 2 rewrite subst_list_val_cons. iApply IHe2; auto. simpl. auto.
  Qed.

  Lemma compat_Fold:
    ∀ e e' : expr,
      open_exprel n e e'
      → open_exprel n (inject TCRec (Fold e)) (Fold e').
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= inject_Closed.
    iApply (lift_bind _ _ _ [FoldCtx; AppRCtx _] [FoldCtx]). iSplitL "". iApply IHe; auto.
    iIntros (v u') "#Hvu'". simpl. iApply lift_step_later. apply inject_step with (v := FoldV v); auto. iNext. change (Fold u') with (of_val $ FoldV u').
    iApply lift_val. iEval (rewrite valrel_unfold). iExists TCRec. iExists _. iSplit; auto. iExists _, _. repeat iSplit; auto.
  Qed.

  Lemma compat_Unfold:
    ∀ e e' : expr,
      open_exprel n e e'
      → open_exprel n (Unfold (extract TCRec e)) (Unfold e').
  Proof.
    intros e e' IHe.
    iIntros (vs vs' Hlvs) "#Hvv's". asimpl.
    rewrite /= extract_Closed.
    iApply (bind_lift_extract [UnfoldCtx] [UnfoldCtx]). iSplitL "". iApply IHe; auto.
    iNext. iIntros (v v') "des/=". iDestruct "des" as (w w') "(-> & -> & #H)".
    iApply lift_step_later. auto_STLCmuVS_step. iApply lift_step. auto_STLCmuVS_step. simplify_custom. iApply lift_val. iApply "H".
  Qed.

  Lemma compat_VirtStep_help : ∀ v v',
      valrel v v' ⊢ valrel v (VirtStepped v').
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
    - iDestruct "Hcan" as (e) "[-> #H]";
        iEval (rewrite valrel_unfold); fold valrel; iExists TCArrow.
      iExists _; iSplit; eauto. simpl. iExists _. iSplit; eauto. iNext.
      iDestruct "H" as "#H". iModIntro.
      iIntros (w w') "Hww'".
      iAssert (valrel w (VirtStepped w')) with "[Hww']" as "Hwws'". by iApply "IHlob".
      iSpecialize ("H" $! w (VirtStepped w') with "Hwws'").
      iApply (wp_wand with "H"). iIntros (v) "Hdes".
      iDestruct "Hdes" as (r) "[%Hsteps #H]".
      iExists (VirtStepped r). iSplit; [|by iApply "IHlob"].
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
        -- assert (abs : to_val (v' (VirtStepped w')) = Some r). by rewrite -to_of_val H1. inversion abs.
        -- destruct stuck. eapply H2. apply H.
    - iDestruct "Hcan" as (x x') "(-> & -> & #H)";
        iEval (rewrite valrel_unfold); fold valrel; iExists TCRec.
      iExists _; eauto. iSplit; eauto. iExists _, _. repeat iSplit; eauto. by iApply "IHlob".
  Qed.

  Lemma compat_VirtStep e e' :
    open_exprel n e e' →
    open_exprel n e (VirtStep e').
  Proof.
    iIntros (IHe vs vs' Hlvs) "#Hvv's". asimpl.
    iApply (lift_bind _ _ _ [] [VirtStepCtx]). iSplitL "". iApply IHe; auto.
    iIntros (v v') "#Hvv'". iClear "Hvv's". simpl.
    iApply lift_rtc_steps. apply VirtStep_eval.
    iApply lift_val. by iApply compat_VirtStep_help.
  Qed.

End syn_le_un.
