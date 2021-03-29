From stdpp Require Export prelude.
From iris Require Export prelude.
From Autosubst Require Export Autosubst.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
  Proof.
    revert x; induction m as [|m IH]=> -[|x];
      repeat (destruct (lt_dec _ _) || asimpl || rewrite IH); auto with lia.
  Qed.


  Lemma iter_up_cases k n σ : (upn n σ k = ids k ∧ k < n) +
                                   { j : nat | (k = (n + j)%nat) ∧ upn n σ k = (σ j).[ren (+n)]  }.
  Proof.
    destruct (decide (k < n)).
    - left. split. rewrite iter_up. destruct (lt_dec k n). auto. exfalso;lia. auto.
    - apply inr. exists (k - n). split. lia. rewrite iter_up. destruct (lt_dec k n).
      contradiction. by asimpl.
  Qed.

  Lemma upn_lt i n σ : i < n → upn n σ i = ids i.
  Proof.
    generalize dependent i.
    induction n.
    - intros. exfalso. lia.
    - intros. destruct i.
      + by asimpl.
      + asimpl. rewrite IHn. by asimpl. lia.
  Qed.

  Definition Closed_n (n : nat) (t : term) : Prop := ∀ σ, t.[upn n σ] = t.
  Definition Closed : term → Prop := Closed_n 0.

  Definition subst_list (vs : list term) : var → term :=
    fun (x : var) => from_option id (ids x) (vs !! x).

  Lemma simul_subst_closed (s t1 t2 : term) (Ct1 : Closed t1) (Ct2 : Closed t2) : s.[t1/].[t2/] = s.[t1,t2/].
  Proof. asimpl. by rewrite Ct1. Qed.

  Lemma scomp_closed_term (t : term) (Ct : Closed t) σ : t .: σ = t .: ids >> σ.
  Proof.
    f_ext. intro x. induction x.
    - by simpl.
    - by asimpl.
  Qed.

  (* Lemma n_closed_invariant n (e : term) s1 s2 : *)
  (*   Closed_n n e → (∀ x, x < n → s1 x = s2 x) → e.[s1] = e.[s2]. *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma subst_list_cons_closed_S_n (t : term) (ts : list term) *)
  (*        (tn : term) (Ctn : Closed_n (S (length ts)) tn) : *)
  (*   tn.[subst_list (t :: ts)] = tn.[up (subst_list ts)].[t/]. *)
  (* Proof. *)
  (*   rewrite subst_comp. apply n_closed_invariant with (n := S (length ts)). *)
  (*   apply Ctn. *)
  (*   intros x px. *)
  (*   rewrite /subst_list. *)
  (*   destruct x. by asimpl. *)
  (*   asimpl. destruct (ts !! x) eqn:eq. *)
  (*   - simpl. by rewrite eq. *)
  (*   - assert (length ts ≤ x). by apply lookup_ge_None_1. *)
  (*     lia. *)
  (* Qed. *)

End Autosubst_Lemmas.
