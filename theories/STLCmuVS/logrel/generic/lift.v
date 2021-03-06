From iris Require Import program_logic.weakestpre.
From st.STLCmuVS Require Import lang wkpre.
From iris.proofmode Require Import tactics.

Section lift.

  Context `{Σ : !gFunctors}.
  Context `{irisGS_inst : !irisGS STLCmuVS_lang Σ}.

  Context (s : stuckness).

  Definition lift (Φ : valO -n> valO -n> iPropO Σ) : exprO → exprO → iProp Σ :=
    fun eᵢ eₛ => (WP eᵢ @ s ; top {{ vᵢ, ∃ vₛ, ⌜ rtc STLCmuVS_step eₛ (of_val vₛ) ⌝ ∧ Φ vᵢ vₛ }})%I.

  Definition liftl (Φ : valO -n> valO -n> iPropO Σ) : exprO → exprO → iProp Σ :=
    fun eₛ eᵢ => (WP eᵢ @ s ; top {{ vᵢ, ∃ vₛ, ⌜ rtc STLCmuVS_step eₛ (of_val vₛ) ⌝ ∧ Φ vₛ vᵢ }})%I.

  Lemma bla eᵢ eₛ Φ : lift Φ eᵢ eₛ ⊣⊢ liftl (λne x x', Φ x' x) eₛ eᵢ.
  Proof. auto. Qed.

  Lemma lift_bind (Φ Ψ : valO -n> valO -n> iPropO Σ) (Kᵢ Kₛ : ectx STLCmuVS_ectx_lang) (eᵢ eₛ : expr) :
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
    by apply (rtc_STLCmuVS_step_ctx (fill Kₛ)).
  Qed.

  Lemma lift_bind' (Φ Ψ : valO -n> valO -n> iPropO Σ) (Kᵢ Kₛ : ectx STLCmuVS_ectx_lang) (eᵢ eₛ : expr) :
    ⊢ lift Φ eᵢ eₛ -∗ (∀ vᵢ vₛ, Φ vᵢ vₛ -∗ lift Ψ (fill Kᵢ (of_val vᵢ)) (fill Kₛ (of_val vₛ))) -∗ lift Ψ (fill Kᵢ eᵢ) (fill Kₛ eₛ).
  Proof. iIntros "HΦeN H". rewrite /lift. iApply lift_bind. iFrame "HΦeN". auto. Qed.

  Lemma lift_bind'' (Kᵢ Kₛ : list ectx_item) (Φ Ψ : valO -n> valO -n> iPropO Σ) (eᵢ eₛ : expr) :
    ⊢ lift Φ eᵢ eₛ -∗ (∀ vᵢ vₛ, Φ vᵢ vₛ -∗ lift Ψ (fill Kᵢ (of_val vᵢ)) (fill Kₛ (of_val vₛ))) -∗ lift Ψ (fill Kᵢ eᵢ) (fill Kₛ eₛ).
  Proof. iApply lift_bind'. Qed.

  Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
  Hint Extern 10 (IntoVal _ _) =>
    rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

  Lemma lift_val (Ψ : valO -n> valO -n> iPropO Σ) (vᵢ vₛ : val) : (Ψ vᵢ vₛ) ⊢ lift Ψ vᵢ vₛ.
  Proof. iIntros "Hv". rewrite /lift. iApply wp_value. iExists vₛ. auto. Qed.

  (* lemmas for impl side; lets only have _later lemmas for lift *)

  Lemma lift_nsteps_later Φ e e' eₛ n (H : nsteps STLCmuVS_step n e e') : ▷^n lift Φ e' eₛ ⊢ lift Φ e eₛ.
  Proof. by iApply wp_nsteps_later. Qed.

  Lemma lift_PureExec_later Φ e e' eₛ n (H : PureExec True n e e') : ▷^n lift Φ e' eₛ ⊢ lift Φ e eₛ.
  Proof. by iApply wp_PureExec_later. Qed.

  Lemma lift_step_later Φ e e' eₛ (H : STLCmuVS_step e e') : ▷ lift Φ e' eₛ ⊢ lift Φ e eₛ.
  Proof. by iApply wp_step_later. Qed.

  (* lemmas for impl side; no_later *)

  Lemma lift_rtc_steps_impl Φ e e' eₛ (H : rtc STLCmuVS_step e e') : lift Φ e' eₛ ⊢ lift Φ e eₛ.
  Proof. by iApply wp_rtc_steps. Qed.

  (* lemmas for spec sideᵢ *)

  Lemma lift_rtc_steps Φ eᵢ e e' (H : rtc STLCmuVS_step e e') : lift Φ eᵢ e' ⊢ lift Φ eᵢ e.
  Proof.
    iIntros "H". iApply (wp_wand with "H").
    iIntros (v) "des". iDestruct "des" as (w') "[%H1 H2]". iExists w'. iFrame "H2".
    iPureIntro. by eapply rtc_transitive.
  Qed.

  Lemma lift_step Φ eᵢ e e' (H : STLCmuVS_step e e') : lift Φ eᵢ e' ⊢ lift Φ eᵢ e.
  Proof. iApply lift_rtc_steps. by apply rtc_once. Qed.

  Lemma lift_impl (Φ Ψ : valO -n> valO -n> iPropO Σ) (H : ∀ v v', Φ v v' ⊢ Ψ v v') :
    ∀ e e', lift Φ e e' ⊢ lift Ψ e e'.
  Proof.
    iIntros (e e') "Hee'". rewrite /lift.
    iApply (wp_wand with "Hee'"). iIntros (v) "Hdes".
    iDestruct "Hdes" as (v') "[%He'v' HΦ]".
    iExists v'. iSplit. auto. by iApply H.
  Qed.

  Lemma lift_equiv (Φ Ψ : valO -n> valO -n> iPropO Σ) (H : ∀ v v', Φ v v' ⊣⊢ Ψ v v') :
    ∀ e e', lift Φ e e' ⊣⊢ lift Ψ e e'.
  Proof. iIntros (e e'). iSplit; iApply lift_impl; iIntros (v v') "Hvv'"; by iApply H. Qed.

  Lemma lift_wand (Φ Ψ : valO -n> valO -n> iPropO Σ) e e' :
    ⊢ (∀ v v', Φ v v' -∗ Ψ v v') -∗ lift Φ e e' -∗ lift Ψ e e'.
  Proof.
    iIntros "H Hee'". rewrite /lift.
    iApply (wp_wand with "Hee'"). iIntros (v) "Hdes".
    iDestruct "Hdes" as (v') "[%He'v' HΦ]".
    iExists v'. iSplit. auto. by iApply "H".
  Qed.

  Lemma anti_step_help e1 e2 v : STLCmuVS_step e1 e2 → rtc STLCmuVS_step e1 (of_val v) → rtc STLCmuVS_step e2 (of_val v).
  Proof.
    intros H Hs.
    inversion Hs; subst.
    - exfalso. assert (to_val v = None) as Hn by eapply (language.val_stuck _ _ _ _ _ _ H).
      by rewrite to_of_val in Hn.
    - by rewrite (prim_step_det _ _ _ _ _ H0 H) in H1.
  Qed.

  Lemma anti_steps_help e1 e2 v : rtc STLCmuVS_step e1 e2 → rtc STLCmuVS_step e1 (of_val v) → rtc STLCmuVS_step e2 (of_val v).
  Proof.
    intros H Hs. destruct (iffLR (rtc_nsteps _ _) H) as [m Hm].
    revert H Hs Hm. revert v e1 e2. induction m.
    - simpl. intros. inversion Hm. by subst.
    - intros. inversion Hm. subst.
      pose proof (anti_step_help _ _ _ H1 Hs).
      eapply (IHm _ _ _ (rtc_nsteps_2 _ _ _ H2) H0 H2).
  Qed.

  Lemma lift_anti_steps_spec Φ eᵢ e1 e2 (H : rtc STLCmuVS_step e1 e2) : lift Φ eᵢ e1 ⊢ lift Φ eᵢ e2.
  Proof.
    iIntros "H". iApply (wp_wand with "H"). iIntros (v) "des".
    iDestruct "des" as (v') "[%Hs H]". iExists v'. iFrame "H".
    iPureIntro. by eapply anti_steps_help.
  Qed.

End lift.

Notation "lift!" := (lift NotStuck).
Notation "lift?" := (lift MaybeStuck).
