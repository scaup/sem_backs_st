From st.lam Require Export types lang typing.

Local Open Scope expr_no_st_scope.
Local Open Scope types_no_st_scope.

Definition FixLam (e : expr) : expr :=
  (Rec (e.[upn 1 (ren (+2))].[%0 %1/]) (Lam e)).

Lemma FixLam_typed Γ e τ (d : τ :: Γ ⊢ₙₒ e : τ) : Γ ⊢ₙₒ FixLam e : τ.
Proof.
  apply App_typed with (τ1 := τ ⟶ τ); try by repeat econstructor. apply Rec_typed.
  apply typed_subst with (τ2 := τ); try by repeat econstructor.
  change ([τ] ++ (τ ⟶ τ) ⟶ τ :: τ ⟶ τ :: [] ++ Γ ⊢ₙₒ e.[upn 1 (ren (+2))] : τ).
  by apply (context_gen_weakening ((τ ⟶ τ) ⟶ τ :: τ ⟶ τ :: [])).
Qed.

Lemma FixLam_step σ κ e : prim_step (FixLam e) σ κ (e.[FixLam e/]) σ [].
Proof.
  apply head_prim_step. rewrite /FixLam.
  assert (e.[Rec e.[upn 1 (ren (+2))].[%0 %1/] (Lam e)/] = e.[upn 1 (ren (+2))].[%0 %1/].[Rec (e.[upn 1 (ren (+2))].[%0 %1/]),(Lam e)/]) as ->. by asimpl.
  by eapply BetaS.
Qed.
