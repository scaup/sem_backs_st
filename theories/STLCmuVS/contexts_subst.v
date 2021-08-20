From st.STLCmuVS Require Import lang typing types contexts scopedness.

Definition subst_ctx_item (σ : var → expr) (Ci : ctx_item) : ctx_item :=
  match Ci with
  | CTX_Lam => CTX_Lam
  | CTX_AppL e2 => CTX_AppL e2.[σ]
  | CTX_AppR e1 => CTX_AppR e1.[σ]
  | CTX_LetInL e2 => CTX_LetInL e2.[up σ]
  | CTX_LetInR e1 => CTX_LetInR e1.[σ]
  | CTX_PairL e2 => CTX_PairL e2.[σ]
  | CTX_PairR e1 => CTX_PairR e1.[σ]
  | CTX_Fst => CTX_Fst
  | CTX_Snd => CTX_Snd
  | CTX_InjL => CTX_InjL
  | CTX_InjR => CTX_InjR
  | CTX_CaseL e1 e2 => CTX_CaseL e1.[up σ] e2.[up σ]
  | CTX_CaseM e0 e2 => CTX_CaseM e0.[σ] e2.[up σ]
  | CTX_CaseR e0 e1 => CTX_CaseR e0.[σ] e1.[up σ]
  | CTX_BinOpL op e2 => CTX_BinOpL op e2.[σ]
  | CTX_BinOpR op e1 => CTX_BinOpR op e1.[σ]
  | CTX_IfL e1 e2 => CTX_IfL e1.[σ] e2.[σ]
  | CTX_IfM e0 e2 => CTX_IfM e0.[σ] e2.[σ]
  | CTX_IfR e0 e1 => CTX_IfR e0.[σ] e1.[σ]
  | CTX_Fold => CTX_Fold
  | CTX_Unfold => CTX_Unfold
  | CTX_VirtStep => CTX_VirtStep
  end.

Definition subst_ctx_item_cont (σ : var → expr) (Ci : ctx_item) : var → expr :=
  match Ci with
  | CTX_Lam => up σ
  | CTX_LetInR e1 => up σ
  | CTX_CaseM e0 e2 => up σ
  | CTX_CaseR e0 e1 => up σ
  | _ => σ
  end.

Lemma subst_fill_ctx_item (σ : var → expr) (Ci : ctx_item) e :
  (fill_ctx_item Ci e).[σ] = fill_ctx_item (subst_ctx_item σ Ci) e.[subst_ctx_item_cont σ Ci].
Proof. destruct Ci; simpl; auto. Qed.

Fixpoint subst_ctx (σ : var → expr) (C : ctx) : ctx :=
  match C with
  | [] => []
  | cons Ci C => subst_ctx_item σ Ci :: (subst_ctx (subst_ctx_item_cont σ Ci) C)
  end.

Fixpoint subst_ctx_cont (σ : var → expr) (C : ctx) : var → expr :=
  match C with
  | nil => σ
  | cons Ci C => subst_ctx_cont (subst_ctx_item_cont σ Ci) C
  end.

Lemma subst_fill_ctx (σ : var → expr) (C : ctx) e :
  (fill_ctx C e).[σ] = fill_ctx (subst_ctx σ C) e.[subst_ctx_cont σ C].
Proof.
  revert σ. induction C as [|Ci C IH]; first done.
  intro σ. by rewrite /= subst_fill_ctx_item IH.
Qed.

Lemma subst_n_closed_ctx_item (σ : var → expr) (Ci : ctx_item) n m (HC : |sCi> n ⊢ₙₒ Ci ☾ m ☽) :
  subst_ctx_item (upn n σ) Ci = Ci.
Proof. destruct HC; asimpl; auto; repeat rewrite (iffRL (expr_Closed_n _ _)); auto. Qed.

Lemma subst_ctx_item_cont_scope Ci σ n m (H : |sCi> n ⊢ₙₒ Ci ☾ m ☽) :
  (upn m σ) = subst_ctx_item_cont (upn n σ) Ci.
Proof. destruct H; simpl; auto. Qed.

Lemma subst_n_closed_ctx (σ : var → expr) (C : ctx) n m (HC : |sC> n ⊢ₙₒ C ☾ m ☽) :
  subst_ctx (upn n σ) C = C.
Proof.
  induction HC; first done.
  simpl. rewrite (subst_n_closed_ctx_item _ _ _ _ H). f_equiv.
  rewrite -(subst_ctx_item_cont_scope k _ n3 n2); auto.
Qed.

Lemma subst_closed_ctx (σ : var → expr) (C : ctx) m (HC : |sC> 0 ⊢ₙₒ C ☾ m ☽) :
  subst_ctx σ C = C.
Proof. cut (subst_ctx (upn 0 σ) C = C). by asimpl. by eapply subst_n_closed_ctx. Qed.

Lemma subst_n_closed_ctx_item_cont (σ : var → expr) (Ci : ctx_item) n m (HC : |sCi> n ⊢ₙₒ Ci ☾ m ☽) :
  subst_ctx_item_cont (upn n σ) Ci = upn m σ.
Proof. destruct HC; asimpl; auto. Qed.

Lemma subst_n_closed_ctx_cont (σ : var → expr) (C : ctx) n m (HC : |sC> n ⊢ₙₒ C ☾ m ☽) :
  subst_ctx_cont (upn n σ) C = upn m σ.
Proof.
  induction HC; first done.
  simpl. by rewrite (subst_n_closed_ctx_item_cont _ _ _ _ H) IHHC.
Qed.

Lemma subst_closed_ctx_cont (σ : var → expr) (C : ctx) m (HC : |sC> 0 ⊢ₙₒ C ☾ m ☽) :
  subst_ctx_cont σ C = upn m σ.
Proof. cut (subst_ctx_cont (upn 0 σ) C = upn m σ). by asimpl. by eapply subst_n_closed_ctx_cont. Qed.
