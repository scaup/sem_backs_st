From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From iris.base_logic.lib Require Import gen_heap.

From st.STLCmuST Require Import lang.
From st.STLCmuVS Require Import lang wkpre.
From st Require Import resources.

Section lift.

  Context `{Σ : !gFunctors} `{sem_le_stΣ_inst : !sem_le_stΣ Σ}.

  Context (s : stuckness).

  Definition lift (Φ : valO -n> STLCmuST.lang.valO -n> iPropO Σ) :
    exprO → STLCmuST.lang.exprO → iProp Σ :=
      fun eᵢ eₛ => (∀ σ : gmap loc STLCmuST.lang.val ,
                    (gen_heap_interp σ -∗ WP eᵢ @ s ; top {{ vᵢ, ∃ vₛ σ', gen_heap_interp σ' ∗ ⌜ rtc STLCmuST_step (σ, eₛ) (σ', STLCmuST.lang.of_val vₛ) ⌝ ∗ Φ vᵢ vₛ }}))%I.

  Lemma lift_bind (Kᵢ : list ectx_item) (Kₛ : list STLCmuST.lang.ectx_item) (Φ Ψ : valO -n> STLCmuST.lang.valO -n> iPropO Σ)
        (eᵢ : expr) (eₛ  : STLCmuST.lang.expr) :
    ⊢ lift Φ eᵢ eₛ -∗ (∀ vᵢ vₛ, Φ vᵢ vₛ -∗ lift Ψ (fill Kᵢ (of_val vᵢ)) (fill Kₛ (STLCmuST.lang.of_val vₛ))) -∗ lift Ψ (fill Kᵢ eᵢ) (fill Kₛ eₛ).
  Proof.
    iIntros "HΦeN H". rewrite /lift. iIntros (σ) "Hσ". iSpecialize ("HΦeN" $! σ with "Hσ").
    iApply (wp_bind' Kᵢ). iApply (wp_wand with "HΦeN").
    iIntros (v). iIntros "des". iDestruct "des" as (v' σ') "(Hσ' & %HNv' & Hvv')".
    iSpecialize ("H" $! v v' with "Hvv'"). iSpecialize ("H" $! σ' with "Hσ'").
    iApply (wp_wand with "H").
    iIntros (w). iIntros "des". iDestruct "des" as (w' σ'') "(Hσ'' & %HKₛv'w' & Hww')".
    iExists w', σ''. iFrame. iPureIntro.
    apply (rtc_transitive _ (σ', fill Kₛ v')); auto.
    by apply fill_STLCmuST_step_rtc.
  Qed.

  Lemma lift_pure_step_rtc Φ eᵢ e e' (H : rtc pure_step e e') : lift Φ eᵢ e' ⊢ lift Φ eᵢ e.
  Proof.
    iIntros "H". iIntros (σ) "Hσ". iSpecialize ("H" $! σ with "Hσ"). iApply (wp_wand with "H").
    iIntros (v) "des". iDestruct "des" as (w' σ') "(Hσ' & %Hsteps & H2)". iExists w'. iFrame "H2".
    iExists σ'. iFrame. iPureIntro. eapply rtc_transitive with (y := (σ, e')); eauto.
    eapply rtc_congruence; eauto. intros. destruct H0. destruct (pure_step_safe σ).
    destruct H0 as (σ'' & efs & primstep).
    by destruct (pure_step_det _ _ _ _ _ primstep) as (eq1 & -> & -> & ->).
  Qed.

  Lemma lift_pure_step Φ eᵢ e e' (H : pure_step e e') : lift Φ eᵢ e' ⊢ lift Φ eᵢ e.
  Proof. iApply lift_pure_step_rtc. by apply rtc_once. Qed.

  Lemma lift_step_later Φ e e' eₛ (H : STLCmuVS_step e e') : ▷ lift Φ e' eₛ ⊢ lift Φ e eₛ.
  Proof. iIntros "H". iIntros (σ) "Hσ". iApply wp_step_later. eauto. by iApply "H". Qed.

  Lemma lift_val (Ψ : valO -n> STLCmuST.lang.valO -n> iPropO Σ) vᵢ vₛ : (Ψ vᵢ vₛ) ⊢ lift Ψ vᵢ vₛ.
  Proof. iIntros "Hv". rewrite /lift. iIntros (σ) "Hσ". iApply wp_value'. iExists vₛ, σ. iFrame. iPureIntro. apply rtc_refl. Qed.

  Lemma lift_val_fupd (Ψ : valO -n> STLCmuST.lang.valO -n> iPropO Σ) vᵢ vₛ : (|={⊤}=> Ψ vᵢ vₛ) ⊢ lift Ψ vᵢ vₛ.
  Proof. iIntros "Hv". rewrite /lift. iIntros (σ) "Hσ". iApply wp_value_fupd'. iExists vₛ, σ. iFrame. iMod "Hv". iModIntro. iSplit; auto. Qed.

  Lemma lift_wand (Φ Ψ : valO -n> STLCmuST.lang.valO -n> iPropO Σ) e e' :
    ⊢ (∀ v v', Φ v v' -∗ Ψ v v') -∗ lift Φ e e' -∗ lift Ψ e e'.
  Proof.
    iIntros "H Hee'". iIntros (σ) "Hσ". iSpecialize ("Hee'" $! σ with "Hσ").
    iApply (wp_wand with "Hee'"). iIntros (v) "Hdes".
    iDestruct "Hdes" as (v' σ') "(Hσ' & %He'v' & HΦ)".
    iExists v', σ'. iFrame. iSplit; auto. by iApply "H".
  Qed.

End lift.
