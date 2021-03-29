From st.lam Require Export types lang typing.

Definition Ω : expr :=
  (Rec (%0 %1) ())%Eₙₒ.

Lemma Ω_loop σ κ : prim_step Ω σ κ Ω σ [].
Proof. apply head_prim_step. rewrite /Ω. by eapply BetaS. Qed.

Lemma Ω_typed Γ τ : Γ ⊢ₙₒ Ω : τ.
Proof.
  rewrite /Ω. eapply App_typed; try by constructor.
  apply Rec_typed. eapply App_typed; by constructor.
Qed.
