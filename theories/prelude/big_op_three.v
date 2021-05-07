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

Section big_sepL3_lemmas.

  Context `{Σ : !gFunctors}.

  Lemma big_sepL3_lookup {A B C}
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

  Lemma big_sepL3_length {A B C}
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

End big_sepL3_lemmas.
