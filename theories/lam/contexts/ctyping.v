From st.lam Require Import lang types typing contexts.definition.

Section context_depth_one.

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
      typed_ctx_item CTX_Unfold Γ (TRec τ) Γ τ.[(TRec τ)/].

  Lemma typed_ctx_item_typed k Γ τ Γ' τ' e :
    typed Γ e τ → typed_ctx_item k Γ τ Γ' τ' →
    typed Γ' (fill_ctx_item k e) τ'.
  Proof. induction 2; simpl; eauto using typed. Qed.

End context_depth_one.

Section context.

  Notation ctx := (list ctx_item).

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

End context.
