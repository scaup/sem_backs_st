From st.STLCmuVS Require Import types lang typing tactics.
From st.backtranslations.un_syn Require Import universe.base.
From st.STLCmuVS.lib Require Import omega.

Opaque Ω.

Local Ltac simplify_custom := (repeat rewrite /= to_of_val; simplify_option_eq; repeat rewrite Ω_Closed).

Lemma eval_same_tc tc v : rtc STLCmuVS_step (CaseTC tc (Unfold (FoldV (InjVTC tc v)))) v.
Proof. destruct tc; by repeat (eapply rtc_l; first auto_STLCmuVS_step; first simplify_custom). Qed.

Lemma eval_diff_tc tc1 tc2 v : tc1 ≠ tc2 → rtc STLCmuVS_step (CaseTC tc1 (Unfold (FoldV (InjVTC tc2 v)))) Ω.
Proof. destruct tc1; destruct tc2; intro neq; (try by contradiction); by repeat ((by eapply rtc_refl) || eapply rtc_l; first auto_STLCmuVS_step; first simplify_custom). Qed.
