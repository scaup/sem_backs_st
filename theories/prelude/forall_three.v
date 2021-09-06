From stdpp Require Export list.

Lemma Forall3_fmap_l {A A' B C : Type} (f : A → A')
    (P : A' → B → C → Prop) (l : list A) (m : list B) (r : list C) :
    Forall3 P (f <$> l) m r ↔ Forall3 (P ∘ f) l m r.
Proof.
  split; revert m r; induction l; inversion_clear 1; constructor; auto.
Qed.

Lemma Forall3_fmap_m {A B B' C : Type} (f : B → B')
    (P : A → B' → C → Prop) (l : list A) (m : list B) (r : list C) :
    Forall3 P l (f <$> m) r ↔ Forall3 (fun a b c => P a (f b) c) l m r.
Proof.
  split; revert l r; induction m; inversion_clear 1; constructor; auto.
Qed.

Lemma Forall3_fmap_r {A B C C' : Type} (f : C → C')
    (P : A → B → C' → Prop) (l : list A) (m : list B) (r : list C) :
    Forall3 P l m (f <$> r) ↔ Forall3 (fun a b c => P a b (f c)) l m r.
Proof.
  split; revert l m; induction r; inversion_clear 1; constructor; auto.
Qed.

Lemma Forall3_same {A : Type} (P : A → A → A → Prop) (l : list A) :
    Forall3 P l l l ↔ Forall (fun a => P a a a) l.
Proof.
  split; induction l; inversion_clear 1; constructor; auto.
Qed.

Lemma Forall3_Forall2 {A B C} (P : A → B → C → Prop) (l1 : list A) (l2 : list B) (l3 : list C) :
  Forall3 P l1 l2 l3 → Forall2 (uncurry P) (zip l1 l2) l3.
Proof. induction 1; constructor; auto. Qed.

Lemma Forall3_superfluous_zip_r {A B} (P : A → B → (A * B) → Prop) (l1 : list A) (l2 : list B) :
  Forall2 (fun a b => P a b (a, b)) l1 l2 → Forall3 P l1 l2 (zip l1 l2).
Proof. induction 1; constructor; auto. Qed.

Lemma Forall3_superfluous_m {A B C} (P : A → C → Prop) (l1 : list A) (l2 : list B) (l3 : list C):
  Forall3 (fun a _ c => P a c) l1 l2 l3 → Forall2 P l1 l3.
Proof. induction 1; constructor; auto. Qed.

(* Lemma Forall3_superfluous_r {A B} (P : A → B → (A * B) → Prop) (l1 : list A) (l2 : list B) : *)
(*   Forall3 P l1 l2 (zip l1 l2) → Forall2 (fun a b => P a b (a, b)) l1 l2. *)
(* Proof. *)
(*   generalize dependent l2. *)
(*   induction l1 as [|a l1]. *)
(*   - intros l2 H; destruct l2;[|by inversion H]. constructor. *)
(*   - intros l2 H. destruct l2 as [|b l2]; [by inversion H|]. inversion_clear H. *)
(*     constructor; auto. *)
(* Qed. *)
