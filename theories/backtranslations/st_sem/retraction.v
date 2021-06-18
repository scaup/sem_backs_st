From st.lamst Require Import lang.
From st.lam Require Import lang.
From st.backtranslations.st_sem Require Import expressions.
From st.embedding Require Import expressions.

Lemma retraction (e : lam.lang.expr) : back_expr (embd_expr e) = e.
Proof.
  induction e; simpl; repeat match goal with
                             | H : _ = _ |- _ => rewrite H
                             end; try done. by destruct l.
Qed.
