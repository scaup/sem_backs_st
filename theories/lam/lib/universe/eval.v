From st.lam Require Import types lang typing tactics.
From st.lam.lib Require Import omega fixlam dummy universe.base.

Opaque Ω.

Ltac simplify_custom := (repeat rewrite /= to_of_val; simplify_option_eq; repeat rewrite Ω_Closed).

Lemma eval_same_tc tc v : rtc lam_step (CaseTC tc (Unfold (FoldV (InjVTC tc v)))) v.
Proof. destruct tc; by repeat (eapply rtc_l; first auto_lam_step; first simplify_custom). Qed.

Lemma eval_diff_tc tc1 tc2 v : tc1 ≠ tc2 → rtc lam_step (CaseTC tc1 (Unfold (FoldV (InjVTC tc2 v)))) Ω.
Proof. destruct tc1; destruct tc2; intro neq; (try by contradiction); by repeat ((by eapply rtc_refl) || eapply rtc_l; first auto_lam_step; first simplify_custom). Qed.
