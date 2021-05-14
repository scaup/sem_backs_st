From iris.base_logic Require Import lib.iprop.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.

Fixpoint big_sepL3 {PROP : bi} {A B C}
    (Φ : A → B → C → PROP) (l1 : list A) (l2 : list B) (l3 : list C) : PROP :=
  match l1, l2, l3 with
  | [], [], [] => emp
  | x1 :: l1, x2 :: l2, x3 :: l3 => Φ x1 x2 x3 ∗ big_sepL3 Φ l1 l2 l3
  | _, _,_ => False
  end%I.

(* From iris Require Import bi.big_op. *)
(* From stdpp Require Import countable fin_sets functions. *)
(* From iris.algebra Require Export big_op. *)
(* From iris.algebra Require Import list gmap. *)
(* From iris.bi Require Import derived_laws_later. *)
(* From iris.prelude Require Import options. *)
(* Import interface.bi derived_laws.bi derived_laws_later.bi. *)


Section big_sepL3_alt.

  Context `{Σ : !gFunctors}.
  Context {A B C : Type}.


  Definition big_sepL3_alt
      (Φ : A → B → C → iProp Σ) (l1 : list A) (l2 : list B) (l3 : list C) : iProp Σ :=
    (⌜ length l1 = length l2 ⌝)%I ∧ big_sepL2 (fun _ ab c => Φ ab.1 ab.2 c) (zip l1 l2) l3.

  Lemma Forall3_same_length (l : list A) (k : list B) (m : list C) :
    Forall3 (λ _ _ _, True) l k m ↔ length l = length k ∧ length k = length m.
  Proof.
    split.
    - induction 1.
      + auto.
      + simpl. lia.
    - revert k m. induction l.
      + intros ?? [? ?]. rewrite -H in H0. simpl in *.
        destruct k, m; simpl in *; try by exfalso. constructor.
      + intros ?? [? ?]. rewrite -H in H0. simpl in *.
        destruct k, m; simpl in *; try by exfalso. constructor; first auto.
        apply IHl; lia.
  Qed.

  Lemma big_sepL3_alt_equiv
      (Φ : A → B → C → iProp Σ) (l1 : list A) (l2 : list B) (l3 : list C) :
    big_sepL3 Φ l1 l2 l3 ⊣⊢ big_sepL3_alt Φ l1 l2 l3.
  Proof.
    rewrite /big_sepL3_alt.
    apply (anti_symm _).
    - apply bi.and_intro.
      + revert l2 l3. induction l1 as [|x1 l1 IH]=> -[|x2 l2] -[|x3 l3] /=; auto.
        iIntros "[H1 H2]". iDestruct (IH with "H2") as %eq. iPureIntro. lia.
      + revert l2 l3. induction l1 as [|x1 l1 IH]=> -[|x2 l2] -[|x3 l3] /=; auto.
        iIntros "[H1 H2]". iFrame "H1". by iApply IH.
    - apply bi.pure_elim_l. intro eq1.
      iIntros "H". iDestruct (big_sepL2_length with "H") as %eq2.
      assert (Hl : Forall3 (fun _ _ _ => True) l1 l2 l3).
      { apply Forall3_same_length. split; auto.
        rewrite -eq2.
        rewrite -(fmap_length snd).
        rewrite snd_zip; auto. lia.
      }
      iInduction Hl as [|x1 x2 x3 l1 l2 l3 aa bb cc] "IH"; auto.
      simpl. iDestruct "H" as "[H1 H2]". iFrame "H1".
      simpl in *.
      assert (eq1' : length l1 = length l2); first lia.
      assert (eq2' : length (zip l1 l2) = length l3); first lia.
      iSpecialize ("IH" $! eq1' eq2').
      iApply ("IH" with "H2").
  Qed.

End big_sepL3_alt.

Section big_sepL3_lemmas.

  Context `{Σ : !gFunctors}.
  Context {A B C : Type}.

  Global Instance big_sepL3_nil_persistent (Φ : A → B → C → iProp Σ) :
    Persistent (big_sepL3 Φ [] [] []).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL3_persistent (Φ : A → B → C → iProp Σ) l1 l2 l3 :
    (∀ x1 x2 x3, Persistent (Φ x1 x2 x3)) →
    Persistent (big_sepL3 Φ l1 l2 l3).
  Proof.
    rewrite big_sepL3_alt_equiv /big_sepL3_alt. apply _.
  Qed.

  (* TODO; clean up versions using alt version *)
  Lemma big_sepL3_lookup
      (Φ : A → B → C → iProp Σ) l1 l2 l3 i x1 x2 x3 :
    l1 !! i = Some x1 → l2 !! i = Some x2 → l3 !! i = Some x3 →
    big_sepL3 Φ l1 l2 l3 ⊢ Φ x1 x2 x3.
  Proof.
    generalize dependent l3.
    generalize dependent l2.
    generalize dependent l1.
    induction i.
    - intros l1 l2 l3 H1 H2 H3. iIntros "H".
      destruct l1 as [|a1 k1]; inversion H1. destruct l2 as [|a2 k2]; inversion H2. destruct l3 as [|a3 k3]; inversion H3.
      simpl. iDestruct "H" as "[a b]". auto.
    - intros l1 l2 l3 H1 H2 H3.
      destruct l1 as [|a1 k1]; inversion H1. destruct l2 as [|a2 k2]; inversion H2. destruct l3 as [|a3 k3]; inversion H3.
      iIntros "H".
      iApply (IHi k1 k2 k3 H0 H4 H5).
      simpl. iDestruct "H" as "[a b]". auto.
  Qed.

  Lemma big_sepL3_length
      (Φ : A → B → C → iProp Σ) l1 l2 l3 : big_sepL3 Φ l1 l2 l3 ⊢ ⌜ length l1 = length l2 ⌝ ∧ ⌜ length l2 = length l3 ⌝.
  Proof.
    generalize dependent l3.
    generalize dependent l2.
    generalize dependent l1.
    induction l1.
    - intros. destruct l2; destruct l3; auto.
    - intros. destruct l2; destruct l3; auto.
      iIntros "H". simpl. rewrite IHl1. iDestruct "H" as "[H %I]". iPureIntro. lia.
  Qed.

  Lemma big_sepL3_fmap_l {A' : Type} (f : A → A') (Φ : A' → B → C → iProp Σ) l1 l2 l3 :
    big_sepL3 (fun a b c => Φ (f a) b c) l1 l2 l3
    ⊣⊢ big_sepL3 (fun a b c => Φ a b c) (f <$> l1) l2 l3.
  Proof.
    generalize dependent l3.
    generalize dependent l2.
    generalize dependent l1.
    induction l1.
    - intros. destruct l2; destruct l3; auto.
    - intros. destruct l2; destruct l3; auto. simpl. specialize (IHl1 l2 l3).
      iSplit; iIntros "[H1 H2]"; iFrame "H1"; by iApply IHl1.
  Qed.

  Lemma big_sepL3_impl (Φ Ψ : A → B → C → iProp Σ) l1 l2 l3 :
    ⊢ big_sepL3 Φ l1 l2 l3 -∗ □ (∀ x1 x2 x3, Φ x1 x2 x3 -∗ Ψ x1 x2 x3) -∗ big_sepL3 Ψ l1 l2 l3.
  Proof.
    generalize dependent l3.
    generalize dependent l2.
    generalize dependent l1.
    induction l1.
    - intros. destruct l2; destruct l3; auto.
    - intros. destruct l2; destruct l3; auto. simpl. specialize (IHl1 l2 l3).
      iIntros "[Habc Hl1l2l3] #Himpl". iSplitL "Habc". by iApply "Himpl". by iApply (IHl1 with "Hl1l2l3").
  Qed.

  (* Lemma big_sepL3_impl (Φ Ψ : A → B → C → iProp Σ) l1 l2 l3 : *)
  (*   ⊢ □ (∀ x1 x2 x3, Φ x1 x2 x3 ∗-∗ Ψ x1 x2 x3) -∗ big_sepL3 Φ l1 l2 l3 ∗-∗ big_sepL3 Ψ l1 l2 l3. *)
  (* Proof. *)
  (*   generalize dependent l3. *)
  (*   generalize dependent l2. *)
  (*   generalize dependent l1. *)
  (*   induction l1. *)
  (*   - intros. destruct l2; destruct l3; auto. *)
  (*   - intros. destruct l2; destruct l3; auto. simpl. specialize (IHl1 l2 l3). *)
  (*     iIntros "#HΦΨ". *)
  (*     iSplit; iIntros "[H1 H2]"; iSplitL "H1 HΦΨ"; try iApply "HΦΨ"; auto; try by iApply IHl1. *)
  (* Qed. *)

End big_sepL3_lemmas.
