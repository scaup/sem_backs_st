From st.lam Require Import lang contexts.
From st.STLCmuST Require Import lang contexts.
From st.embedding Require Import expressions types typed.

Definition embd_ctx_item (Ci : lam.contexts.ctx_item) : ctx_item :=
  match Ci with
  | lam.contexts.CTX_Lam => CTX_Lam
  | lam.contexts.CTX_AppL e2 => CTX_AppL [[e2]]
  | lam.contexts.CTX_AppR e1 => CTX_AppR [[e1]]
  | lam.contexts.CTX_LetInL e2 => CTX_LetInL [[e2]]
  | lam.contexts.CTX_LetInR e1 => CTX_LetInR [[e1]]
  | lam.contexts.CTX_PairL e2 => CTX_PairL [[e2]]
  | lam.contexts.CTX_PairR e1 => CTX_PairR [[e1]]
  | lam.contexts.CTX_Fst => CTX_Fst
  | lam.contexts.CTX_Snd => CTX_Snd
  | lam.contexts.CTX_InjL => CTX_InjL
  | lam.contexts.CTX_InjR => CTX_InjR
  | lam.contexts.CTX_CaseL e1 e2 => CTX_CaseL [[e1]] [[e2]]
  | lam.contexts.CTX_CaseM e0 e2 => CTX_CaseM [[e0]] [[e2]]
  | lam.contexts.CTX_CaseR e0 e1 => CTX_CaseR [[e0]] [[e1]]
  | lam.contexts.CTX_BinOpL op e2 => CTX_BinOpL op [[e2]]
  | lam.contexts.CTX_BinOpR op e1 => CTX_BinOpR op [[e1]]
  | lam.contexts.CTX_IfL e1 e2 => CTX_IfL [[e1]] [[e2]]
  | lam.contexts.CTX_IfM e0 e2 => CTX_IfM [[e0]] [[e2]]
  | lam.contexts.CTX_IfR e0 e1 => CTX_IfR [[e0]] [[e1]]
  | lam.contexts.CTX_Fold => CTX_Fold
  | lam.contexts.CTX_Unfold => CTX_Unfold
  | lam.contexts.CTX_GhostStep => CTX_Lam (* we only care about embedding syntactically well-typed expressions *)
  end.

Lemma embd_ctx_item_typed (Ci : lam.contexts.ctx_item) (Γ : list lam.types.type) (τ : lam.types.type) (Γ' : list lam.types.type) (τ' : lam.types.type) :
  lam.contexts.typed_ctx_item Ci Γ τ Γ' τ' →
  STLCmuST.contexts.typed_ctx_item (embd_ctx_item Ci) (fmap embed Γ) (embed τ) (fmap embed Γ') (embed τ').
Proof.
  intro dCi.
  inversion dCi; try by (econstructor; (try rewrite -fmap_cons); eapply embd_typed).
  - econstructor. change (types.TArrow [|τ|] [|τ'|]) with ([|lam.types.TArrow τ τ'|]). by eapply embd_typed.
  - apply TP_CTX_CaseM with (τ2 := [|τ2|]). change (types.TSum [|?τ1|] [|?τ2|]) with ([|lam.types.TSum τ1 τ2|]). by eapply embd_typed.
    rewrite -fmap_cons. by eapply embd_typed.
  - apply TP_CTX_CaseR with (τ1 := [|τ1|]). change (types.TSum [|?τ1|] [|?τ2|]) with ([|lam.types.TSum τ1 τ2|]). by eapply embd_typed.
    rewrite -fmap_cons. by eapply embd_typed.
  - apply TP_CTX_IfM. change (types.TBool) with ([|lam.types.TBool|]). by eapply embd_typed.
    by eapply embd_typed.
  - apply TP_CTX_IfR. change (types.TBool) with ([|lam.types.TBool|]). by eapply embd_typed.
    by eapply embd_typed.
  - destruct op; simpl; econstructor; change (types.TInt) with ([|lam.types.TInt|]); by eapply embd_typed.
  - destruct op; simpl; econstructor; change (types.TInt) with ([|lam.types.TInt|]); by eapply embd_typed.
  - rewrite embed_TRec_comm. econstructor.
  - rewrite embed_TRec_comm. econstructor.
Qed.

Definition embd_ctx (C : lam.contexts.ctx) : ctx :=
  fmap embd_ctx_item C.

Lemma embd_ctx_typed (C : lam.contexts.ctx) (Γ : list lam.types.type) (τ : lam.types.type) (Γ' : list lam.types.type) (τ' : lam.types.type) :
  lam.contexts.typed_ctx C Γ τ Γ' τ' → STLCmuST.contexts.typed_ctx (embd_ctx C) (fmap embed Γ) (embed τ) (fmap embed Γ') (embed τ').
Proof.
  intro de. induction de; try by econstructor.
  econstructor. by apply embd_ctx_item_typed. apply IHde.
Qed.

Lemma comm_fill_ctx_item_embd (Ci : lam.contexts.ctx_item) (e : lam.lang.expr) :
  STLCmuST.contexts.fill_ctx_item (embd_ctx_item Ci) (embd_expr e) =
  embd_expr (lam.contexts.fill_ctx_item Ci e).
Proof. by destruct Ci; simpl. Qed.

Lemma comm_fill_ctx_embd (C : lam.contexts.ctx) (e : lam.lang.expr) :
  STLCmuST.contexts.fill_ctx (embd_ctx C) (embd_expr e) =
  embd_expr (lam.contexts.fill_ctx C e).
Proof.
  induction C; simpl; first done.
  by rewrite IHC comm_fill_ctx_item_embd.
Qed.
