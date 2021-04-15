From iris Require Import program_logic.weakestpre.
From st.lam Require Import lang wkpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Canonical Structure valO := valO lam_lang.
Canonical Structure exprO := exprO lam_lang.

Section lift.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Context (s : stuckness).

  Definition lift (Φ : valO -n> valO -n> iPropO Σ) : exprO → exprO → iProp Σ :=
    fun eᵢ eₛ => (WP eᵢ @ s ; top {{ vᵢ, ∃ vₛ, ⌜ rtc lam_step eₛ (of_val vₛ) ⌝ ∧ Φ vᵢ vₛ }})%I.

  Definition liftl (Φ : valO -n> valO -n> iPropO Σ) : exprO → exprO → iProp Σ :=
    fun eₛ eᵢ => (WP eᵢ @ s ; top {{ vᵢ, ∃ vₛ, ⌜ rtc lam_step eₛ (of_val vₛ) ⌝ ∧ Φ vₛ vᵢ }})%I.

  Lemma bla eᵢ eₛ Φ : lift Φ eᵢ eₛ ⊣⊢ liftl (λne x x', Φ x' x) eₛ eᵢ.
  Proof. auto. Qed.

  Lemma lift_bind (Φ Ψ : valO -n> valO -n> iPropO Σ) (Kᵢ Kₛ : ectx lam_ectx_lang) (eᵢ eₛ : expr) :
    (lift Φ eᵢ eₛ ∗ ∀ vᵢ vₛ, Φ vᵢ vₛ -∗ lift Ψ (fill Kᵢ (of_val vᵢ)) (fill Kₛ (of_val vₛ))) ⊢ lift Ψ (fill Kᵢ eᵢ) (fill Kₛ eₛ).
  Proof.
    iIntros "[HΦeN H]". rewrite /lift.
    iApply wp_bind. iApply (wp_wand with "HΦeN").
    iIntros (v). iIntros "des". iDestruct "des" as (v') "[%HNv' Hvv']".
    iSpecialize ("H" $! v v' with "Hvv'").
    iApply (wp_wand with "H").
    iIntros (w). iIntros "des". iDestruct "des" as (w') "[%HKₛv'w' Hww']".
    iExists w'. iFrame. iPureIntro.
    apply (rtc_transitive _ (fill Kₛ v')); auto. simpl in *.
    by apply (rtc_lam_step_ctx (fill Kₛ)).
  Qed.

  Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
  Hint Extern 10 (IntoVal _ _) =>
    rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

  Lemma lift_val (Ψ : valO -n> valO -n> iPropO Σ) (vᵢ vₛ : val) : (Ψ vᵢ vₛ) ⊢ lift Ψ vᵢ vₛ.
  Proof. iIntros "Hv". rewrite /lift. iApply wp_value. iExists vₛ. auto. Qed.

  (* lemmas for impl side; lets only have _later lemmas for lift; applying iNext is easy enough *)

  Lemma lift_nsteps_later Φ e e' eₛ n (H : nsteps lam_step n e e') : ▷^n lift Φ e' eₛ ⊢ lift Φ e eₛ.
  Proof. by iApply wp_nsteps_later. Qed.

  Lemma lift_PureExec_later Φ e e' eₛ n (H : PureExec True n e e') : ▷^n lift Φ e' eₛ ⊢ lift Φ e eₛ.
  Proof. by iApply wp_PureExec_later. Qed.

  Lemma lift_step_later Φ e e' eₛ (H : lam_step e e') : ▷ lift Φ e' eₛ ⊢ lift Φ e eₛ.
  Proof. by iApply wp_step_later. Qed.

  (* lemmas for spec sideᵢ *)

  Lemma lift_rtc_steps Φ eᵢ e e' (H : rtc lam_step e e') : lift Φ eᵢ e' ⊢ lift Φ eᵢ e.
  Proof.
    iIntros "H". iApply (wp_wand with "H").
    iIntros (v) "des". iDestruct "des" as (w') "[%H1 H2]". iExists w'. iFrame "H2".
    iPureIntro. by eapply rtc_transitive.
  Qed.

  Lemma lift_step Φ eᵢ e e' (H : lam_step e e') : lift Φ eᵢ e' ⊢ lift Φ eᵢ e.
  Proof. iApply lift_rtc_steps. by apply rtc_once. Qed.

End lift.

Notation "lift!" := (lift NotStuck).
Notation "lift?" := (lift MaybeStuck).
