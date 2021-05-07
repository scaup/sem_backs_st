From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Section expl_idx.

  Context `{Σ : !gFunctors}.

  (* Definition expl_idx (n : nat) (P : iProp Σ) : Prop := ▷^n False ⊢ P. *)
  Notation expl_idx n P := (@bi_entails (uPredI (iResUR Σ)) (▷^n False)%I P).

  Import uPred.
  Arguments uPred_holds {_} !_.

  Lemma false_n_lt n : ∀ k x, (k < n <-> @uPred_holds (iResUR Σ) ((▷^n False)%I) k x).
  Proof.
    induction n.
    - unseal. auto with lia.
    - intros k. simpl. unseal. destruct k. auto with lia.
      specialize (IHn k). revert IHn. unseal. intros IHn. split.
      + intros Hsksn. apply IHn. lia.
      + intros Hnk. apply lt_n_S. by apply (IHn x).
  Qed.

  Lemma expl_idx' n P : expl_idx n P <-> ∀ k, k < n → uPred_holds P k ε.
  Proof.
    split.
    - intros [HnP]. intros k Hkn.
      apply HnP. apply ucmra_unit_validN. by apply false_n_lt.
    - intros HP. constructor. intros k x Hx Hs.
      apply uPred_mono with (n1 := k) (x1 := ε); eauto using ucmra_unit_leastN.
      apply HP. by apply (false_n_lt n k x).
  Qed.

  Lemma expl_idx_S_n (n : nat) (P : iProp Σ) : expl_idx (S n) (▷ P) <-> expl_idx n P.
  Proof.
    split.
    - rewrite !expl_idx'. unseal. simpl. intros HK k Hkn.
      apply (HK (S k)). lia.
    - intro HP. iIntros "Fsn". iNext. by iApply HP.
  Qed.

  Lemma expl_idx_S_n_exists {A : Type} `{!Inhabited A} (n : nat) (P : A → iProp Σ) :
    expl_idx n (∃ a, P a) <-> ∃ a, expl_idx n (P a).
  Proof.
    split.
    - setoid_rewrite expl_idx'. intros Hk.
      destruct n.
      + simpl. exists inhabitant. lia.
      + revert Hk. unseal. intros Hk. destruct (Hk n) as [a Hpa].
        lia. exists a. intros k Hksn. eapply uPred_mono; eauto with lia.
    - destruct 1 as [a HPa]. iIntros "HF". iExists a. by iApply HPa.
  Qed.

  Lemma expl_idx_S_n_pure (n : nat) (P : Prop) :
    expl_idx (S n) ⌜ P ⌝ <-> P.
  Proof.
    split.
    - rewrite expl_idx'. unseal. intros Hk. apply (Hk 0). lia.
    - intro HP. iIntros "Fsn". auto.
  Qed.

  Lemma expl_idx_and (n : nat) (P Q : iProp Σ) :
    expl_idx n (P ∧ Q) <-> expl_idx n P ∧ expl_idx n Q.
  Proof.
    split.
    - intros HPQ. split.
      + iIntros "Hn". iDestruct (HPQ with "Hn") as "HH". by iApply and_elim_l.
      + iIntros "Hn". iDestruct (HPQ with "Hn") as "HH". by iApply and_elim_r.
    - intros [HP HQ]. iIntros "HF". iSplit; [by iApply HP | by iApply HQ].
  Qed.

  Lemma expl_idx_sep (n : nat) (P Q : iProp Σ) :
    expl_idx n (P ∗ Q) <-> expl_idx n P ∧ expl_idx n Q.
  Proof.
    split.
    - intros HPQ. split.
      + iIntros "Hn". iDestruct (HPQ with "Hn") as "HH". by iApply sep_elim_l.
      + iIntros "Hn". iDestruct (HPQ with "Hn") as "HH". by iApply sep_elim_r.
    - intros [HP HQ]. iIntros "#HF". iSplitL; [by iApply HP | by iApply HQ].
  Qed.

  (* Lemma expl_idx_and' (n : nat) (P Q : iProp Σ) : (* same proof in the model *) *)
  (*   expl_idx n (P ∧ Q) → expl_idx n P ∧ expl_idx n Q. *)
  (* Proof. *)
  (*   rewrite !expl_idx'. unseal. intros Hk; split; intros; apply Hk; done. *)
  (* Qed. *)

  Lemma alt_proof (P : iProp Σ) : (∀ n, expl_idx n P) → ⊢ P.
  Proof.
    setoid_rewrite expl_idx'. intros Hn. constructor. intros.
    eapply uPred_mono; [ apply (Hn (S n) n) |  | ]; auto using ucmra_unit_leastN with lia.
  Qed.

  Lemma map_expl_idx (P Q : iProp Σ) n : (P ⊢ Q) → (expl_idx n P → expl_idx n Q).
  Proof.
    iIntros (HPQ HnP) "HnF". iApply HPQ. by iApply HnP.
  Qed.

End expl_idx.
