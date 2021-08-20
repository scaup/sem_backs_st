From st.STLCmuVS Require Import lang (* just for bin_op *).
From st.STLCmuST Require Import lang typing types.

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
    | CTX_Unfold
    | CTX_Alloc
    | CTX_Read
    | CTX_WriteL (e2 : expr)
    | CTX_WriteR (e1 : expr)
    | CTX_CompL (e2 : expr)
    | CTX_CompR (e1 : expr)
    | CTX_Return
    | CTX_BindL (e2: expr)
    | CTX_BindR (e1: expr)
    | CTX_RunST.

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
    | CTX_Alloc => Alloc e
    | CTX_Read => Read e
    | CTX_WriteL e2 => Write e e2
    | CTX_WriteR e1 => Write e1 e
    | CTX_CompL e2 => Compare e e2
    | CTX_CompR e1 => Compare e1 e
    | CTX_Return => Return e
    | CTX_BindL e2 => Bind e e2
    | CTX_BindR e1 => Bind e1 e
    | CTX_RunST => RunST e
    end.

  Inductive typed_ctx_item :
      ctx_item → list type → type → list type → type → Prop :=
    | TP_CTX_Lam Γ τ τ' :
      typed_ctx_item CTX_Lam (τ :: Γ) τ' Γ (TArrow τ τ')
    | TP_CTX_AppL Γ e2 τ τ' :
      typed Γ e2 τ →
      typed_ctx_item (CTX_AppL e2) Γ (TArrow τ τ') Γ τ'
    | TP_CTX_AppR Γ e1 τ τ' :
      typed Γ e1 (TArrow τ τ') →
      typed_ctx_item (CTX_AppR e1) Γ τ Γ τ'
    | TP_CTX_LetInL Γ e2 τ τ' :
        typed (τ :: Γ) e2 τ' →
        typed_ctx_item (CTX_LetInL e2) Γ τ Γ τ'
    | TP_CTX_LetInR Γ e1 τ τ' :
        typed Γ e1 τ →
        typed_ctx_item (CTX_LetInR e1) (τ :: Γ) τ' Γ τ'
    | TP_CTX_PairL Γ e2 τ τ' :
      typed Γ e2 τ' →
      typed_ctx_item (CTX_PairL e2) Γ τ Γ (TProd τ τ')
    | TP_CTX_PairR Γ e1 τ τ' :
      typed Γ e1 τ →
      typed_ctx_item (CTX_PairR e1) Γ τ' Γ (TProd τ τ')
    | TP_CTX_Fst Γ τ τ' :
      typed_ctx_item CTX_Fst Γ (TProd τ τ') Γ τ
    | TP_CTX_Snd Γ τ τ' :
      typed_ctx_item CTX_Snd Γ (TProd τ τ') Γ τ'
    | TP_CTX_InjL Γ τ τ' :
      typed_ctx_item CTX_InjL Γ τ Γ (TSum τ τ')
    | TP_CTX_InjR Γ τ τ' :
      typed_ctx_item CTX_InjR Γ τ' Γ (TSum τ τ')
    | TP_CTX_CaseL Γ e1 e2 τ1 τ2 τ' :
      typed (τ1 :: Γ) e1 τ' → typed (τ2 :: Γ) e2 τ' →
      typed_ctx_item (CTX_CaseL e1 e2) Γ (TSum τ1 τ2) Γ τ'
    | TP_CTX_CaseM Γ e0 e2 τ1 τ2 τ' :
      typed Γ e0 (TSum τ1 τ2) → typed (τ2 :: Γ) e2 τ' →
      typed_ctx_item (CTX_CaseM e0 e2) (τ1 :: Γ) τ' Γ τ'
    | TP_CTX_CaseR Γ e0 e1 τ1 τ2 τ' :
      typed Γ e0 (TSum τ1 τ2) → typed (τ1 :: Γ) e1 τ' →
      typed_ctx_item (CTX_CaseR e0 e1) (τ2 :: Γ) τ' Γ τ'
    | TP_CTX_IfL Γ e1 e2 τ :
      typed Γ e1 τ → typed Γ e2 τ →
      typed_ctx_item (CTX_IfL e1 e2) Γ (TBool) Γ τ
    | TP_CTX_IfM Γ e0 e2 τ :
      typed Γ e0 (TBool) → typed Γ e2 τ →
      typed_ctx_item (CTX_IfM e0 e2) Γ τ Γ τ
    | TP_CTX_IfR Γ e0 e1 τ :
      typed Γ e0 (TBool) → typed Γ e1 τ →
      typed_ctx_item (CTX_IfR e0 e1) Γ τ Γ τ
    | TP_CTX_BinOpL op Γ e2 :
      typed Γ e2 TInt →
      typed_ctx_item (CTX_BinOpL op e2) Γ TInt Γ (binop_res_type op)
    | TP_CTX_BinOpR op e1 Γ :
      typed Γ e1 TInt →
      typed_ctx_item (CTX_BinOpR op e1) Γ TInt Γ (binop_res_type op)
    | TP_CTX_Fold Γ τ :
      typed_ctx_item CTX_Fold Γ τ.[(TRec τ)/] Γ (TRec τ)
    | TP_CTX_Unfold Γ τ :
      typed_ctx_item CTX_Unfold Γ (TRec τ) Γ τ.[(TRec τ)/]
    | TPCTX_Alloc Γ ρ τ :
      typed_ctx_item CTX_Alloc Γ τ Γ (TST ρ (TSTref ρ τ))
    | TP_CTX_Read Γ ρ τ :
      typed_ctx_item CTX_Read Γ (TSTref ρ τ) Γ (TST ρ τ)
    | TP_CTX_WriteL Γ e2 ρ τ :
      typed Γ e2 τ →
      typed_ctx_item (CTX_WriteL e2) Γ (TSTref ρ τ) Γ (TST ρ TUnit)
    | TP_CTX_WriteR Γ e1 ρ τ :
      typed Γ e1 (TSTref ρ τ) →
      typed_ctx_item (CTX_WriteR e1) Γ τ Γ (TST ρ TUnit)
    | TP_CTX_CompL Γ e2 ρ τ :
        typed Γ e2 (TSTref ρ τ) →
        typed_ctx_item (CTX_CompL e2) Γ (TSTref ρ τ) Γ TBool
    | TP_CTX_CompR Γ e1 ρ τ :
        typed Γ e1 (TSTref ρ τ) →
        typed_ctx_item (CTX_CompR e1) Γ (TSTref ρ τ) Γ TBool
    | TP_CTX_Return Γ ρ τ :
        typed_ctx_item CTX_Return Γ τ Γ (TST ρ τ)
    | TP_CTX_BindL Γ e2 ρ τ τ':
        typed Γ e2 (TArrow τ (TST ρ τ')) →
        typed_ctx_item (CTX_BindL e2) Γ (TST ρ τ) Γ (TST ρ τ')
    | TP_CTX_BindR Γ e1 ρ τ τ' :
        typed Γ e1 (TST ρ τ) →
        typed_ctx_item (CTX_BindR e1) Γ (TArrow τ (TST ρ τ')) Γ (TST ρ τ')
    | TP_CTX_RunST Γ τ :
        typed_ctx_item CTX_RunST (subst (ren (+1)) <$>Γ)
                      (TST (TVar 0) τ.[ren (+1)]) Γ τ.

  Lemma typed_ctx_item_typed k Γ τ Γ' τ' e :
    typed Γ e τ → typed_ctx_item k Γ τ Γ' τ' →
    typed Γ' (fill_ctx_item k e) τ'.
  Proof. induction 2; simpl; eauto using typed. Qed.

End context_depth_one.

Section context.

  Definition ctx := (list ctx_item).

  (* Does not define fill convention as in ectxi_language! *)
  Definition fill_ctx (K : ctx) (e : expr) : expr := foldr (fill_ctx_item) e K.

  Lemma fill_ctx_behavior Ki K e : fill_ctx (Ki :: K) e = fill_ctx_item Ki (fill_ctx K e).
  Proof. by simpl. Qed.

  Inductive typed_ctx : ctx → list type → type → list type → type → Prop :=
    | TPCTX_nil Γ τ :
      typed_ctx nil Γ τ Γ τ
    | TPCTX_cons Γ1 τ1 Γ2 τ2 Γ3 τ3 k K :
      typed_ctx_item k Γ2 τ2 Γ3 τ3 →
      typed_ctx K Γ1 τ1 Γ2 τ2 →
      typed_ctx (k :: K) Γ1 τ1 Γ3 τ3.

  Lemma typed_ctx_typed K Γ τ Γ' τ' e :
    typed Γ e τ → typed_ctx K Γ τ Γ' τ' → typed Γ' (fill_ctx K e) τ'.
  Proof. induction 2; simpl; eauto using typed_ctx_item_typed. Qed.

  Lemma fill_ctx_app e K K' : fill_ctx K' (fill_ctx K e) = fill_ctx (K' ++ K) e.
  Proof. revert K. induction K' => K; simpl; auto. by rewrite IHK'. Qed.

  Lemma typed_ctx_app Γ Γ' Γ'' K K' τ τ' τ'' :
    typed_ctx K' Γ' τ' Γ'' τ'' →
    typed_ctx K Γ τ Γ' τ' →
    typed_ctx (K' ++ K) Γ τ Γ'' τ''.
  Proof.
    revert K Γ Γ' Γ'' τ τ' τ''; induction K' => K Γ Γ' Γ'' τ τ' τ''; simpl.
    - by inversion 1; subst.
    - intros Htc1 Htc2. inversion Htc1; subst.
      econstructor; last eapply IHK'; eauto.
  Qed.

  (* Alternative that follows the convention *)
  Definition fill_ctx' (K : ctx) (e : expr) : expr := foldl (flip fill_ctx_item) e K.

  Lemma fill_ctx'_behavior Ki e K : (fill_ctx' (Ki :: K) e = fill_ctx' K (fill_ctx_item Ki e)).
  Proof. by simpl. Qed.

End context.
