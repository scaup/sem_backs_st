From stdpp Require Import relations.
Require Import st.prelude.generic.

Definition at_least_one {A : Type} (R : relation A) : relation A :=
  fun x y => ∃ n, 1 ≤ n ∧ nsteps R n x y.

Lemma at_least_one_once {A : Type} (R : relation A) (x y : A) : R x y → at_least_one R x y.
Proof. intros. exists 1. split; [lia | ]. by apply nsteps_once. Qed.

Lemma at_least_one_l {A : Type} (R : relation A) (x y z : A) : R x y → rtc R y z → at_least_one R x z.
Proof. intros. destruct (iffLR (rtc_nsteps _ _) H0) as [n Hn]. exists (S n). split; [lia | ]. eapply nsteps_l; eauto. Qed.

Lemma at_least_one_r {A : Type} (R : relation A) (x y z : A) : rtc R x y → R y z → at_least_one R x z.
Proof. intros. destruct (iffLR (rtc_nsteps _ _) H) as [n Hn]. exists (S n). split; [lia | ]. eapply nsteps_r; eauto. Qed.

Definition at_least_one_rtc {A : Type} (R : relation A) x y : at_least_one R x y → rtc R x y.
Proof. destruct 1 as [n [_ H]]. eapply rtc_nsteps. eauto. Qed.

Definition at_least_one_nsteps {A : Type} (R : relation A) x y : at_least_one R x y → ∃ n, nsteps R n x y.
Proof. eauto. destruct 1 as [n [_ H]]. eauto. Qed.

Lemma at_least_one_split_l {A : Type} (R : relation A) x z : at_least_one R x z → ∃ y, R x y ∧ rtc R y z.
Proof. destruct 1 as [n [H H']]. destruct H'. lia. exists y. split; auto. eapply rtc_nsteps. eauto. Qed.

Lemma at_least_one_split_r {A : Type} (R : relation A) x z : at_least_one R x z → ∃ y, rtc R x y ∧ R y z.
Proof. destruct 1 as [n [H H']]. destruct n. lia. destruct (nsteps_inv_r _ _ _ H') as [y [P P']]. exists y. split; auto. by eapply rtc_nsteps; eauto. Qed.
