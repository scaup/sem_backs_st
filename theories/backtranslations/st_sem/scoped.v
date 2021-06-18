From st.lamst Require Import typing lang contexts.
From st.lam Require Import lang scopedness contexts.
From st.backtranslations.st_sem Require Import heap_emul.base expressions contexts.

Opaque alloc read write bind retrn runst.

Lemma back_expr_scope Γ e τ :
  lamst.typing.typed Γ e τ → expr_scoped (length Γ) <<e>>.
Proof.
  intro de. induction de; constructor; try done.
  - by eapply lookup_lt_Some.
  - apply expr_Closed_n; intro σ; by rewrite alloc_Closed.
  - apply expr_Closed_n; intro σ; by rewrite read_Closed.
  - constructor; auto. apply expr_Closed_n; intro σ; by rewrite write_Closed.
  - constructor; auto. apply expr_Closed_n; intro σ; by rewrite bind_Closed.
  - apply expr_Closed_n; intro σ; by rewrite retrn_Closed.
  - apply expr_Closed_n; intro σ; by rewrite runst_Closed.
  - by rewrite fmap_length in IHde.
Qed.

Lemma back_ctx_item_scope Ci Γ τ Γ' τ' :
  lamst.contexts.typed_ctx_item Ci Γ τ Γ' τ' → ctx_scoped (back_ctx_item Ci) (length Γ) (length Γ').
Proof.
  intro dCi.
  destruct dCi;
    try by ((repeat econstructor);
            (try match goal with
                 | H : typed (?τ :: ?Γ) ?e ?τ2 |- expr_scoped (S (length _)) _  =>
                   change (S (length Γ)) with (length (τ :: Γ)); by eapply back_expr_scope
                 end); eapply back_expr_scope).
  - do 2 econstructor. apply expr_Closed_n; intro σ; by rewrite alloc_Closed.
  - do 2 econstructor. apply expr_Closed_n; intro σ; by rewrite read_Closed.
  - do 2 econstructor. by eapply back_expr_scope. constructor. apply expr_Closed_n; intro σ; by rewrite write_Closed. constructor.
  - do 3 econstructor. apply expr_Closed_n; intro σ; by rewrite write_Closed.
    by eapply back_expr_scope.
  - do 2 econstructor. apply expr_Closed_n; intro σ; by rewrite retrn_Closed.
  - do 2 econstructor; auto. by eapply back_expr_scope. econstructor. apply expr_Closed_n; intro σ; by rewrite bind_Closed.
    econstructor.
  - do 3 econstructor; auto. apply expr_Closed_n; intro σ; by rewrite bind_Closed.
      by eapply back_expr_scope.
  - econstructor; auto. econstructor. apply expr_Closed_n; intro σ; by rewrite runst_Closed.
    rewrite fmap_length. constructor.
Qed.

Lemma scoped_ctx_app n n' n'' K K' :
  |sC> n'' ⊢ₙₒ K' ☾ n' ☽ →
  |sC> n' ⊢ₙₒ K ☾ n ☽ →
  |sC> n'' ⊢ₙₒ (K' ++ K) ☾ n ☽.
Proof.
  revert K n n' n''; induction K'; intros.
  - by inversion H; subst.
  - inversion H; subst.
    econstructor; last eapply IHK'; eauto.
Qed.

Lemma back_ctx_scope C Γ τ Γ' τ' :
  lamst.contexts.typed_ctx C Γ τ Γ' τ' → ctx_scoped (back_ctx C) (length Γ) (length Γ').
Proof.
  intro dC. induction dC.
  - by constructor.
  - simpl. eapply scoped_ctx_app. by eapply back_ctx_item_scope. done.
Qed.
