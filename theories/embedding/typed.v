From st.lam Require Import lang typing types.
From st.STLCmuST Require Import lang typing types.
From st.embedding Require Import expressions types.

Lemma embd_typed (Γ : list lam.types.type) (e : lam.lang.expr) (τ : lam.types.type) :
  lam.typing.typed Γ e τ → STLCmuST.typing.typed (fmap embed Γ) (embd_expr e) (embed τ).
Proof.
  intro de. induction de; try by econstructor.
  - constructor. by rewrite list_lookup_fmap H.
  - destruct op; by econstructor.
  - simpl. constructor. by rewrite -embed_TRec_comm.
  - rewrite embed_TRec_comm. by constructor.
Qed.
