From st.lam Require Import lang tactics.

Fixpoint GhostStepped (v : val) : val :=
  match v with
  | LamV e => LamV (GhostStep ((Lam e).[ren (+1)] (GhostStep %0)))%Eₙₒ
  | LitV v => LitV v
  | PairV v1 v2 => PairV (GhostStepped v1) (GhostStepped v2)
  | InjLV v => InjLV (GhostStepped v)
  | InjRV v => InjRV (GhostStepped v)
  | FoldV v => FoldV (GhostStepped v)
  end.

Lemma GhostStep_eval (v : val) : rtc lam_step (GhostStep v) (GhostStepped v).
Proof.
  induction v.
  - apply rtc_once. apply head_prim_step. apply GhostStep_Lam_head_step.
  - apply rtc_once. auto_lam_step.
  - eapply rtc_l. auto_lam_step. simplify_custom.
    eapply rtc_transitive.
    apply (rtc_lam_step_ctx (fill_item (PairLCtx _))). apply IHv1.
    apply (rtc_lam_step_ctx (fill_item (PairRCtx _))). apply IHv2.
  - eapply rtc_l. auto_lam_step. simplify_custom.
    apply (rtc_lam_step_ctx (fill_item InjLCtx)). apply IHv.
  - eapply rtc_l. auto_lam_step. simplify_custom.
    apply (rtc_lam_step_ctx (fill_item InjRCtx)). apply IHv.
  - eapply rtc_l. auto_lam_step. simplify_custom.
    apply (rtc_lam_step_ctx (fill_item FoldCtx)). apply IHv.
Qed.
