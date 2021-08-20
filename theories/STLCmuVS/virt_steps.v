From st.STLCmuVS Require Import lang tactics.

Fixpoint VirtStepped (v : val) : val :=
  match v with
  | LamV e => LamV (VirtStep ((Lam e).[ren (+1)] (VirtStep %0)))%Eₙₒ
  | LitV v => LitV v
  | PairV v1 v2 => PairV (VirtStepped v1) (VirtStepped v2)
  | InjLV v => InjLV (VirtStepped v)
  | InjRV v => InjRV (VirtStepped v)
  | FoldV v => FoldV (VirtStepped v)
  end.

Lemma VirtStep_eval (v : val) : rtc STLCmuVS_step (VirtStep v) (VirtStepped v).
Proof.
  induction v.
  - apply rtc_once. apply head_prim_step. apply VirtStep_Lam_head_step.
  - apply rtc_once. auto_STLCmuVS_step.
  - eapply rtc_l. auto_STLCmuVS_step. simplify_custom.
    eapply rtc_transitive.
    apply (rtc_STLCmuVS_step_ctx (fill_item (PairLCtx _))). apply IHv1.
    apply (rtc_STLCmuVS_step_ctx (fill_item (PairRCtx _))). apply IHv2.
  - eapply rtc_l. auto_STLCmuVS_step. simplify_custom.
    apply (rtc_STLCmuVS_step_ctx (fill_item InjLCtx)). apply IHv.
  - eapply rtc_l. auto_STLCmuVS_step. simplify_custom.
    apply (rtc_STLCmuVS_step_ctx (fill_item InjRCtx)). apply IHv.
  - eapply rtc_l. auto_STLCmuVS_step. simplify_custom.
    apply (rtc_STLCmuVS_step_ctx (fill_item FoldCtx)). apply IHv.
Qed.
