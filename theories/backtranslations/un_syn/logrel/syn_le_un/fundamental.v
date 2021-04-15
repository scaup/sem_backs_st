From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.lam Require Import lang wkpre generic.lift types lib.universe.base tactics lib.universe.eval lib.omega.
From st.backtranslations.un_syn Require Import logrel.definitions expressions.

Section syn_le_un.

  Instance rfn : refinement := syn_le_un.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Lemma wp_Ω Φ : ⊢ WP Ω {{Φ}}.
  Proof. iLöb as "IH". iApply wp_nsteps_later. by apply Ω_loop. done. Qed.

  Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
  Hint Extern 10 (IntoVal _ _) =>
    rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.


  Lemma bind_lift_extract (K K' : ectx lam_ectx_lang) (e e' : expr) (tc : type_constructor):
      exprel e e' ∗ (▷ ∀ v v', canon_tc_lift tc valrel v v' -∗ lift! valrel (fill K (of_val v)) (fill K' (of_val v'))) ⊢
        lift! valrel (fill K (extract tc e)) (fill K' e').
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

  Lemma back_expr_in_relation (e : expr) (n : nat) (pne : Closed_n n e) :
    open_exprel n (back_expr e) e pne.
  Proof.
    generalize dependent n.
    induction e; iIntros (n pne vs vs' Hlvs) "#Hvv's".
    - (* var *) rewrite /back_expr. destruct (Var_subst_list_closed_n_length vs x) as [v [eqv ->]]. by simplify_eq.
      iDestruct (big_sepL2_length with "Hvv's") as %Hl.
      destruct (Var_subst_list_closed_n_length vs' x) as [v' [eqv' ->]]. rewrite -Hl. by simplify_eq.
      rewrite /exprel /=. iApply lift_val.
      iApply ((big_sepL2_lookup _ vs vs' x _ _ eqv eqv') with "Hvv's").
    - (* let in *) admit.
    - (* lam *) rewrite /= inject_Closed.
      iApply lift_step_later. eapply (inject_step _ _ (LamV _)). auto. iNext.
      change (Lam e.[up (subst_list_val vs')]) with (of_val $ LamV e.[up (subst_list_val vs')]). iApply lift_val.
      rewrite valrel_unfold. iExists TCArrow. fold valrel. iExists (LamV <<e>>.[up (subst_list_val vs)]). iSplit; auto.
      simpl. iExists _ , _. iSplit. auto. iSplit. auto.
      do 2 iModIntro. iIntros (w w') "#Hww'". specialize (IHe (S n)). asimpl. do 2 rewrite subst_list_val_cons.
      iApply IHe. closed_solver. simpl. lia. simpl. auto.
    (* - (* fix *) rewrite /= extract_Closed. *)
    (*   iApply (bind_lift_extract [FixCtx] [FixCtx]). *)
    (*   iSplitL "". iApply IHe; auto. closed_solver. clear e IHe pne. *)
    (*   iNext. iIntros (v v') "#Hdes". *)
    (*   simpl. iLöb as "HiLob". *)
    (*   iDestruct "Hdes" as (e e') "(-> & -> & #H)". *)
    (*   iApply wp_step_later. auto_lam_step. *)
    (*   iNext. simpl. iApply lift_steps. apply rtc_once. auto_lam_step. simpl. *)
    (*   admit. *)
    - (* app *) asimpl. rewrite extract_Closed.
      iApply (bind_lift_extract [AppLCtx _] [AppLCtx _]).
      iSplitL "". iApply IHe1; auto. closed_solver. iNext.
      iIntros (v v') "des". simpl. iDestruct "des" as (e e') "(-> & -> & #H)".
      iApply (lift_bind _ _ _ [AppRCtx _] [AppRCtx _]). iSplitL "". iApply IHe2; auto. closed_solver.
      iIntros (w w') "Hww'". simpl. iApply lift_step_later. auto_lam_step. iApply lift_step. auto_lam_step.
      simplify_custom. iNext. iApply ("H" with "Hww'").
    - (* lit *) rewrite /=; destruct l; asimpl; rewrite inject_Closed.
      + iApply lift_step_later. eapply (inject_step _ _ n0); auto. change (Lit n0) with (of_val n0). iApply lift_val.
        rewrite valrel_unfold. iExists TCInt. iExists _. iSplit; auto. simpl. iExists n0 ; (iSplit; eauto).
      + iApply lift_step_later. eapply (inject_step _ _ b); auto. change (Lit b) with (of_val b). iApply lift_val.
        rewrite valrel_unfold. iExists TCBool. iExists _; iSplit; auto. simpl. iExists _ ; (iSplit; eauto).
      + iApply lift_step_later. eapply (inject_step _ _ ()%Vₙₒ); auto. change ()%Eₙₒ with (of_val ()%Vₙₒ). iApply lift_val.
        rewrite valrel_unfold. iExists TCUnit. iExists _; iSplit; auto.
    - (* binop *)
      admit.
    - (* if *)
      admit.
    - (* seq *) rewrite /= extract_Closed.
      iApply (bind_lift_extract [SeqCtx _] [SeqCtx _]). iSplitL "". iApply IHe1; auto. closed_solver. iNext. simpl.
      iIntros (v v') "[-> ->]". iApply lift_step_later. auto_lam_step. iApply lift_step. auto_lam_step. simpl.
      iApply IHe2; auto. closed_solver.
    - (* pair *) asimpl. rewrite inject_Closed.
      iApply (lift_bind _ _ _ [PairLCtx _; AppRCtx _] [PairLCtx _]). iSplitL "". iApply IHe1; auto. closed_solver. iIntros (u1 v1') "#IHu1v1'". simpl.
      iApply (lift_bind _ _ _ [PairRCtx _; AppRCtx _] [PairRCtx _]). iSplitL "". iApply IHe2; auto. closed_solver. iIntros (u2 v2') "#IHu2v2'". simpl.
      iApply lift_step_later. apply inject_step with (v := PairV u1 u2); eauto.
      change (v1',v2')%Eₙₒ with (of_val (v1',v2')%Vₙₒ). iApply lift_val.
      iEval (rewrite valrel_unfold). iExists TCProd. iExists _. iSplit; auto. iExists _, _, _, _. repeat iSplit; done.
    - (* Fst *) rewrite /= extract_Closed.
      iApply (bind_lift_extract [FstCtx] [FstCtx]). iSplitL "". iApply IHe; auto. closed_solver.
      iNext. iIntros (v v') "des/=". iDestruct "des" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
      iApply lift_step_later. auto_lam_step. iApply lift_step. auto_lam_step. simplify_custom. iApply lift_val. done.
    - (* Snd *) rewrite /= extract_Closed.
      iApply (bind_lift_extract [SndCtx] [SndCtx]). iSplitL "". iApply IHe; auto. closed_solver.
      iNext. iIntros (v v') "des/=". iDestruct "des" as (v1 v2 v1' v2') "(-> & -> & #H1 & #H2)".
      iApply lift_step_later. auto_lam_step. iApply lift_step. auto_lam_step. simplify_custom. iApply lift_val. done.
    - (* InjL *) rewrite /= inject_Closed.
      iApply (lift_bind _ _ _ [InjLCtx; AppRCtx _] [InjLCtx]). iSplitL "". iApply IHe; auto. closed_solver.
      iIntros (v u') "#Hvu'". simpl.
      iApply lift_step_later. apply inject_step with (v := InjLV v). auto. iNext. change (InjL u') with (of_val (InjLV u')).
      iApply lift_val. iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; auto. iExists _, _. repeat iSplit; auto.
    - (* InjR *) rewrite /= inject_Closed.
      iApply (lift_bind _ _ _ [InjRCtx; AppRCtx _] [InjRCtx]). iSplitL "". iApply IHe; auto. closed_solver.
      iIntros (v u') "#Hvu'". simpl.
      iApply lift_step_later. apply inject_step with (v := InjRV v). auto. iNext. change (InjR u') with (of_val (InjRV u')).
      iApply lift_val. iEval (rewrite valrel_unfold). iExists TCSum. iExists _. iSplit; auto. iExists _, _. repeat iSplit; auto.
    - (* Case *) rewrite /= extract_Closed.
      iApply (bind_lift_extract [CaseCtx _ _] [CaseCtx _ _]). iSplitL "". iApply IHe; auto. closed_solver.
      iNext. iIntros (v v') "des/=". iDestruct "des" as (vi vi') "[(-> & -> & #Hi)|(-> & -> & #Hi)]".
      + iApply lift_step_later. auto_lam_step. iApply lift_step. auto_lam_step. simplify_custom. asimpl.
        iNext. do 2 rewrite subst_list_val_cons. iApply IHe0; auto. closed_solver. simpl. auto.
      + iApply lift_step_later. auto_lam_step. iApply lift_step. auto_lam_step. simplify_custom. asimpl.
        iNext. do 2 rewrite subst_list_val_cons. iApply IHe1; auto. closed_solver. simpl. auto.
    - (* Fold *) rewrite /= inject_Closed.
      iApply (lift_bind _ _ _ [FoldCtx; AppRCtx _] [FoldCtx]). iSplitL "". iApply IHe; auto. closed_solver.
      iIntros (v u') "#Hvu'". simpl. iApply lift_step_later. apply inject_step with (v := FoldV v); auto. iNext. change (Fold u') with (of_val $ FoldV u').
      iApply lift_val. iEval (rewrite valrel_unfold). iExists TCRec. iExists _. iSplit; auto. iExists _, _. repeat iSplit; auto.
    - (* unfold *) rewrite /= extract_Closed.
      iApply (bind_lift_extract [UnfoldCtx] [UnfoldCtx]). iSplitL "". iApply IHe; auto. closed_solver.
      iNext. iIntros (v v') "des/=". iDestruct "des" as (w w') "(-> & -> & #H)".
      iApply lift_step_later. auto_lam_step. iApply lift_step. auto_lam_step. simplify_custom. iApply lift_val. iApply "H".
  Admitted.

End syn_le_un.
