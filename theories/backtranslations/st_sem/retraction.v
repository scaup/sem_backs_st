From st.STLCmuST Require Import lang contexts.
From st.STLCmuVS Require Import lang contexts typing.
From st.backtranslations.st_sem Require Import expressions contexts.
From st.embedding Require Import expressions contexts.

Lemma retraction Γ (e : STLCmuVS.lang.expr) τ : Γ ⊢ₙₒ e : τ → back_expr (embd_expr e) = e.
Proof.
  intro d.
  induction d; simpl; repeat match goal with
                             | H : _ = _ |- _ => rewrite H
                             end; try done.
Qed.

Lemma retraction_ctx_item (Ci : STLCmuVS.contexts.ctx_item) Γ τ Γ' τ' (dCi : typed_ctx_item Ci Γ τ Γ' τ') : back_ctx_item (embd_ctx_item Ci) = [Ci].
Proof. destruct dCi; simpl; try done; by erewrite !retraction. Qed.

Lemma retraction_ctx (C : STLCmuVS.contexts.ctx) Γ τ Γ' τ' (dC : typed_ctx C Γ τ Γ' τ') : back_ctx (embd_ctx C) = C.
Proof. induction dC; simpl; first done. erewrite retraction_ctx_item; eauto. by rewrite IHdC. Qed.
