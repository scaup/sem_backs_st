From iris.program_logic Require Import language ectxi_language ectx_language lifting.
From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.prelude Require Import at_least_one.
From st.STLCmuVS Require Import lang reducibility.

Section wkpre_lemmas.

  Context `{Σ : !gFunctors}.
  Context `{irisGS_inst : !irisGS STLCmuVS_lang Σ}.

  Lemma wp_bind' (K : list ectx_item) s E e Φ :
    WP e @ s; E {{ v, WP fill K (of_val v) @ s; E {{ Φ }} }} ⊢ WP fill K e @ s; E {{ Φ }}.
  Proof. iApply wp_bind. Qed.

  (* Steps with later *)
  Lemma wp_nsteps_later {s : stuckness} {E : coPset} e1 e2 n Φ (H : nsteps STLCmuVS_step n e1 e2) :
    ▷^n WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof. iIntros "He2". iApply wp_pure_step_later. apply nsteps_PureExec. exact H. auto. done. Qed.

  Lemma wp_step_later {s : stuckness} {E : coPset} e1 e2 Φ (H : STLCmuVS_step e1 e2) :
    ▷ WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof. iIntros "He2". iApply wp_pure_step_later. by eapply step_PureExec. auto. auto. Qed.

  Lemma wp_PureExec_later {s : stuckness} {E : coPset} e1 e2 Φ n (H : PureExec True n e1 e2) :
    ▷^n WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof. iIntros "He2". iApply wp_pure_step_later. auto. auto. Qed.

  Lemma wp_rtc_steps {s : stuckness} {E : coPset} e1 e2 Φ (H : rtc STLCmuVS_step e1 e2) :
    WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof.
    destruct (iffLR (rtc_PureExec _ _) H) as [n H'].
    iIntros "H". iApply wp_pure_step_later. auto. auto.
  Qed.

  Lemma wp_at_least_one_later {s : stuckness} {E : coPset} e1 e2 Φ (H : at_least_one STLCmuVS_step e1 e2) :
    ▷ WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof. destruct (at_least_one_split_l _ _ _ H) as [y [H' H'']]. iIntros "He2". iApply wp_step_later. eauto. by iApply wp_rtc_steps. Qed.

  Lemma wp_at_least_one_step_fupd {s : stuckness} {E E' : coPset} Φ (e1 e2 : expr) :
    at_least_one STLCmuVS_step e1 e2 → (|={E}[E']▷=> WP e2 @ s; E {{ v, Φ v }}) -∗ WP e1 @ s; E {{ v, Φ v }}.
  Proof.
    iIntros (Hone) "H". destruct (at_least_one_split_l _ _ _ Hone) as [y [H H']].
    iApply wp_pure_step_fupd. by apply step_PureExec. auto. simpl. iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    by iApply wp_rtc_steps.
  Qed.

  Lemma wp_Maybestuck_True (e : expr) : ⊢ WP e ? {{ v , True }}.
  Proof.
    revert e. iLöb as "H". iIntros (e).
    destruct (dec_expr_reducibility e) as [v1 eq1 | is_red1 | is_stuck1 ]; first rewrite -(of_to_val _ _ eq1).
    - by iApply wp_value'.
    - assert (is_red : STLCmuVS_reducible e) by by apply STLCmuVS_prim_red. destruct is_red as [e' Hs].
      iApply wp_step_later. apply Hs. iNext. iApply "H".
    - iApply wp_lift_pure_stuck; auto. by intro σ; destruct σ.
  Qed.

  Lemma wp_stuck Φ (e : expr) (H : stuck e tt) : ⊢ WP e ?{{ v, Φ v }}.
  Proof. apply wp_lift_pure_stuck. intro σ. by destruct σ. Qed.

End wkpre_lemmas.
