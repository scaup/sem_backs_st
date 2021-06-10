From st.lam Require Import lang typing types.

Section context_depth_one.

  Inductive ctx_item :=
    | CTX_Lam
    | CTX_AppL (e2 : expr)
    | CTX_AppR (e1 : expr)
    | CTX_LetInL (e2 : expr)
    | CTX_LetInR (e1 : expr)
    | CTX_PairL (e2 : expr)
    | CTX_PairR (e1 : expr)
    | CTX_Fst
    | CTX_Snd
    | CTX_InjL
    | CTX_InjR
    | CTX_CaseL (e1 : expr) (e2 : expr)
    | CTX_CaseM (e0 : expr) (e2 : expr)
    | CTX_CaseR (e0 : expr) (e1 : expr)
    | CTX_BinOpL (op : bin_op) (e2 : expr)
    | CTX_BinOpR (op : bin_op) (e1 : expr)
    | CTX_IfL (e1 : expr) (e2 : expr)
    | CTX_IfM (e0 : expr) (e2 : expr)
    | CTX_IfR (e0 : expr) (e1 : expr)
    | CTX_Fold
    | CTX_Unfold.

  Definition fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
    match ctx with
    | CTX_Lam => Lam e
    | CTX_AppL e2 => App e e2
    | CTX_AppR e1 => App e1 e
    | CTX_LetInL e2 => LetIn e e2
    | CTX_LetInR e1 => LetIn e1 e
    | CTX_PairL e2 => Pair e e2
    | CTX_PairR e1 => Pair e1 e
    | CTX_Fst => Fst e
    | CTX_Snd => Snd e
    | CTX_InjL => InjL e
    | CTX_InjR => InjR e
    | CTX_CaseL e1 e2 => Case e e1 e2
    | CTX_CaseM e0 e2 => Case e0 e e2
    | CTX_CaseR e0 e1 => Case e0 e1 e
    | CTX_BinOpL op e2 => BinOp op e e2
    | CTX_BinOpR op e1 => BinOp op e1 e
    | CTX_IfL e1 e2 => If e e1 e2
    | CTX_IfM e0 e2 => If e0 e e2
    | CTX_IfR e0 e1 => If e0 e1 e
    | CTX_Fold => Fold e
    | CTX_Unfold => Unfold e
    end.

End context_depth_one.

Section context.

  Notation ctx := (list ctx_item).

  (* Does not define fill convention as in ectxi_language! *)
  Definition fill_ctx (K : ctx) (e : expr) : expr := foldr (fill_ctx_item) e K.

  Lemma fill_ctx_behavior Ki K e : fill_ctx (Ki :: K) e = fill_ctx_item Ki (fill_ctx K e).
  Proof. by simpl. Qed.

  Lemma fill_ctx_app e K K' : fill_ctx K' (fill_ctx K e) = fill_ctx (K' ++ K) e.
  Proof. revert K. induction K' => K; simpl; auto. by rewrite IHK'. Qed.

  (* Alternative that follows the convention *)
  Definition fill_ctx' (K : ctx) (e : expr) : expr := foldl (flip fill_ctx_item) e K.

  Lemma fill_ctx'_behavior Ki e K : (fill_ctx' (Ki :: K) e = fill_ctx' K (fill_ctx_item Ki e)).
  Proof. by simpl. Qed.

End context.
