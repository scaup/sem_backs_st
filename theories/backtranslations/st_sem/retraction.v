From st.lamst Require Import lang contexts.
From st.lam Require Import lang contexts.
From st.backtranslations.st_sem Require Import expressions contexts.
From st.embedding Require Import expressions contexts.

Lemma retraction (e : lam.lang.expr) : back_expr (embd_expr e) = e.
Proof.
  induction e; simpl; repeat match goal with
                             | H : _ = _ |- _ => rewrite H
                             end; try done. by destruct l.
Qed.

Lemma retraction_ctx_item (Ci : lam.contexts.ctx_item) : back_ctx_item (embd_ctx_item Ci) = [Ci].
Proof. destruct Ci; simpl; try done; by rewrite !retraction. Qed.

Lemma retraction_ctx (C : lam.contexts.ctx) : back_ctx (embd_ctx C) = C.
Proof. induction C; simpl; first done. by rewrite retraction_ctx_item IHC. Qed.
