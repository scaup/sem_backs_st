From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

From st.lam Require Import lang.
From st.lamst Require Import lang wkpre.

Section lift.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lamst_lang Σ}.

  Context (s : stuckness).

  Definition lift (Φ : valO -n> lam.lang.valO -n> iPropO Σ) : exprO → lam.lang.exprO → iProp Σ :=
    fun eᵢ eₛ => (WP eᵢ @ s ; top {{ vᵢ, ∃ vₛ, ⌜ rtc lam_step eₛ (lam.lang.of_val vₛ) ⌝ ∧ Φ vᵢ vₛ }})%I.

  Lemma lift_bind (Kᵢ : list ectx_item) (Kₛ : list lam.lang.ectx_item) (Φ Ψ : valO -n> lam.lang.valO -n> iPropO Σ)
        (eᵢ : expr) (eₛ  : lam.lang.expr) :
    ⊢ lift Φ eᵢ eₛ -∗ (∀ vᵢ vₛ, Φ vᵢ vₛ -∗ lift Ψ (fill Kᵢ (of_val vᵢ)) (fill Kₛ (lam.lang.of_val vₛ))) -∗ lift Ψ (fill Kᵢ eᵢ) (fill Kₛ eₛ).
  Proof.
    iIntros "HΦeN H". rewrite /lift.
    iApply wp_bind'. iApply (wp_wand with "HΦeN").
    iIntros (v). iIntros "des". iDestruct "des" as (v') "[%HNv' Hvv']".
    iSpecialize ("H" $! v v' with "Hvv'").
    iApply (wp_wand with "H").
    iIntros (w). iIntros "des". iDestruct "des" as (w') "[%HKₛv'w' Hww']".
    iExists w'. iFrame. iPureIntro.
    apply (rtc_transitive _ (fill Kₛ v')); auto. simpl in *.
    by apply (rtc_lam_step_ctx (fill Kₛ)).
  Qed.

  Lemma lift_rtc_steps Φ eᵢ e e' (H : rtc lam_step e e') : lift Φ eᵢ e' ⊢ lift Φ eᵢ e.
  Proof.
    iIntros "H". iApply (wp_wand with "H").
    iIntros (v) "des". iDestruct "des" as (w') "[%H1 H2]". iExists w'. iFrame "H2".
    iPureIntro. by eapply rtc_transitive.
  Qed.

  Lemma lift_pure_step_later Φ e e' eₛ (H : pure_step e e') : ▷ lift Φ e' eₛ ⊢ lift Φ e eₛ.
  Proof. by iApply wp_pure_step_later. Qed.

  Lemma lift_step Φ eᵢ e e' (H : lam_step e e') : lift Φ eᵢ e' ⊢ lift Φ eᵢ e.
  Proof. iApply lift_rtc_steps. by apply rtc_once. Qed.

  Lemma lift_val (Ψ : valO -n> lam.lang.valO -n> iPropO Σ) vᵢ vₛ : (Ψ vᵢ vₛ) ⊢ lift Ψ vᵢ vₛ.
  Proof. iIntros "Hv". rewrite /lift. iApply wp_value'. iExists vₛ. auto. Qed.

  Lemma lift_val_fupd (Ψ : valO -n> lam.lang.valO -n> iPropO Σ) vᵢ vₛ : (|={⊤}=> Ψ vᵢ vₛ) ⊢ lift Ψ vᵢ vₛ.
  Proof. iIntros "Hv". rewrite /lift. iApply wp_value_fupd'. iExists vₛ. iMod "Hv". iModIntro. iSplit; auto. Qed.

  Lemma lift_wand (Φ Ψ : valO -n> lam.lang.valO -n> iPropO Σ) e e' :
    ⊢ (∀ v v', Φ v v' -∗ Ψ v v') -∗ lift Φ e e' -∗ lift Ψ e e'.
  Proof.
    iIntros "H Hee'". rewrite /lift.
    iApply (wp_wand with "Hee'"). iIntros (v) "Hdes".
    iDestruct "Hdes" as (v') "[%He'v' HΦ]".
    iExists v'. iSplit. auto. by iApply "H".
  Qed.

End lift.