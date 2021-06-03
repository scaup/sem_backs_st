From iris.program_logic Require Import language ectxi_language ectx_language lifting.
From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.lam Require Import lang tactics.
From st.prelude Require Import at_least_one.

Section wkpre_lemmas.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Lemma wp_bind' (K : list ectx_item) s E e Φ :
    WP e @ s; E {{ v, WP fill K (of_val v) @ s; E {{ Φ }} }} ⊢ WP fill K e @ s; E {{ Φ }}.
  Proof. iApply wp_bind. Qed.

  (* Steps with later *)
  Lemma wp_nsteps_later {s : stuckness} {E : coPset} e1 e2 n Φ (H : nsteps lam_step n e1 e2) :
    ▷^n WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof. iIntros "He2". iApply wp_pure_step_later. apply nsteps_PureExec. exact H. auto. done. Qed.

  Lemma wp_step_later {s : stuckness} {E : coPset} e1 e2 Φ (H : lam_step e1 e2) :
    ▷ WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof. iIntros "He2". iApply wp_pure_step_later. by eapply step_PureExec. auto. auto. Qed.

  Lemma wp_PureExec_later {s : stuckness} {E : coPset} e1 e2 Φ n (H : PureExec True n e1 e2) :
    ▷^n WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof. iIntros "He2". iApply wp_pure_step_later. auto. auto. Qed.

  Lemma wp_rtc_steps {s : stuckness} {E : coPset} e1 e2 Φ (H : rtc lam_step e1 e2) :
    WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof.
    destruct (iffLR (rtc_PureExec _ _) H) as [n H'].
    iIntros "H". iApply wp_pure_step_later. auto. auto.
  Qed.

  Lemma wp_at_least_one_later {s : stuckness} {E : coPset} e1 e2 Φ (H : at_least_one lam_step e1 e2) :
    ▷ WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof. destruct (at_least_one_split_l _ _ _ H) as [y [H' H'']]. iIntros "He2". iApply wp_step_later. eauto. by iApply wp_rtc_steps. Qed.

  Lemma wp_at_least_one_step_fupd {s : stuckness} {E E' : coPset} Φ (e1 e2 : expr) :
    at_least_one lam_step e1 e2 → (|={E}[E']▷=> WP e2 @ s; E {{ v, Φ v }}) -∗ WP e1 @ s; E {{ v, Φ v }}.
  Proof.
    iIntros (Hone) "H". destruct (at_least_one_split_l _ _ _ Hone) as [y [H H']].
    iApply wp_pure_step_fupd. by apply step_PureExec. auto. simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    by iApply wp_rtc_steps.
  Qed.

  (* things with stuckness *)
  Definition lam_head_step (e e' : expr) := head_step e tt [] e' tt [].

  Lemma head_to_lam_head (e e' : expr) σ σ' κ efs : head_step e σ κ e' σ' efs → lam_head_step e e'.
  Proof. intro H. rewrite /lam_head_step. inversion H; by econstructor. Qed.

  Definition lam_reducible (e : expr) := ∃ e', lam_step e e'.

  Definition lam_irreducible (e : expr) := ∀ e', ¬ lam_step e e'.

  Lemma prim_to_lam (e1 e2 : expr) σ1 σ2 κ efs : prim_step e1 σ1 κ e2 σ2 efs -> lam_step e1 e2.
  Proof. intro H. apply lam_pure. apply (prim_step_pure _ _ _ _ _ _ H). Qed.

  Lemma lam_prim_red (e : expr) : lam_reducible e <-> reducible e tt.
  Proof.
    split. intro H. destruct H as [e' Hstep]. exists [], e', tt, []. apply Hstep.
    intro H. destruct H as (a & e' & b & c & Hstep). exists e'. by eapply prim_to_lam.
  Qed.

  Definition lam_head_reducible (e : expr) := ∃ e', lam_head_step e e'.
  Definition lam_head_irreducible (e : expr) := ∀ e', ¬ lam_head_step e e'.

  Lemma lam_head_red_iff_head_red (e : expr) : lam_head_reducible e <-> head_reducible e tt.
  Proof.
    split. intro H. destruct H as [e' Hstep]. exists [], e', tt, []. apply Hstep.
    intro H. destruct H as (a & e' & b & c & Hstep). exists e'. destruct Hstep; by econstructor.
  Qed.

  Lemma lam_head_irred_iff_head_irred (e : expr) : lam_head_irreducible e <-> head_irreducible e tt.
  Proof.
    split. intro H. intros κ e' σ efs abs. apply (H e'). by eapply head_to_lam_head.
    intros H e' Hstep. apply (H [] e' () []). auto.
  Qed.

  Instance dec_expr_reducible (e : expr) : Decision (reducible e tt).
  Proof.
  Admitted.

  Lemma wp_Maybestuck_True (e : expr) : ⊢ WP e ? {{ v , True }}.
  Proof.
    revert e. iLöb as "H". iIntros (e).
    destruct (decide (reducible e tt)).
    - destruct r as [aa [e' [cc [dd Hstep]]]].
      destruct cc.
      assert (dd = []) as eq. by eapply prim_step_no_forks. rewrite eq in Hstep.
      assert (aa = []) as eq1. by eapply prim_step_no_obs. rewrite eq1 in Hstep.
      iApply wp_step_later. apply Hstep. iNext. iApply "H".
    - destruct (decide (to_val e = None)).
      iApply wp_lift_pure_stuck. intro σ. destruct σ. split; auto. by apply not_reducible. auto.
      destruct (to_val e) eqn:eq. iApply (wp_value _ _ _ _ v). eapply of_to_val; fast_done. auto.
      contradiction.
  Qed.

  Lemma wp_stuck Φ (e : expr) (H : stuck e tt) : ⊢ WP e ?{{ v, Φ v }}.
  Proof. apply wp_lift_pure_stuck. intro σ. by destruct σ. Qed.

End wkpre_lemmas.

Ltac head_stuck_solver :=
  lazymatch goal with
  | |- stuck ?e () => apply head_stuck_stuck; head_stuck_solver
  | |- head_stuck ?e () => split; head_stuck_solver
  | |- rtc lam_step _ _ => (eapply rtc_l; first (auto_lam_step); simplify_custom)
  | |- ectx_language.to_val _ = _ => (by simplify_custom) ; head_stuck_solver
  | |- head_irreducible _ () => ((apply lam_head_irred_iff_head_irred; intros e' abs; inversion abs; simplify_option_eq); try done); head_stuck_solver
  | |- sub_redexes_are_values _ => apply ectxi_language_sub_redexes_are_values; intros Ki' e' eq; destruct Ki'; inversion eq; head_stuck_solver
  | |- is_Some _ => (by eexists; simplify_custom) ; head_stuck_solver
  | |- _ => auto
  end.
