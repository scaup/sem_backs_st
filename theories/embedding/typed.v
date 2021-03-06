From st.STLCmuVS Require Import lang typing.
From st.STLCmu Require Import types.
From st.STLCmuST Require Import lang typing types.
From st.embedding Require Import expressions types.

Lemma embd_typed (Γ : list STLCmu.types.type) (e : STLCmuVS.lang.expr) (τ : STLCmu.types.type) :
  STLCmuVS.typing.typed Γ e τ → STLCmuST.typing.typed (fmap embed Γ) (embd_expr e) (embed τ).
Proof.
  intro de. induction de; try by econstructor.
  - constructor. by rewrite list_lookup_fmap H.
  - destruct op; by econstructor.
  - simpl. constructor. by rewrite -embed_TRec_comm.
  - rewrite embed_TRec_comm. by constructor.
Qed.
