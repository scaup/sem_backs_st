From st.lam Require Import lang types typing.

Inductive expr_scoped (n : nat) : expr → Prop :=
 | Var_scoped x :
     x < n →
     expr_scoped n (Var x)
 | LetIn_scoped e1 e2 :
     expr_scoped n e1 →
     expr_scoped (S n) e2 →
     expr_scoped n (LetIn e1 e2)
 | Lam_scoped e :
     expr_scoped (S n) e →
     expr_scoped n (Lam e)
 | App_scoped e1 e2 :
     expr_scoped n e1 →
     expr_scoped n e2 →
     expr_scoped n (App e1 e2)
 | Lit_scoped (l : base_lit) :
     expr_scoped n (Lit l)
 | BinOp_scoped op e1 e2 :
     expr_scoped n e1 →
     expr_scoped n e2 →
     expr_scoped n (BinOp op e1 e2)
 | If_scoped e0 e1 e2 :
     expr_scoped n e0 →
     expr_scoped n e1 →
     expr_scoped n e2 →
     expr_scoped n (If e0 e1 e2)
 | Seq_scoped e1 e2 :
     expr_scoped n e1 →
     expr_scoped n e2 →
     expr_scoped n (Seq e1 e2)
 | Pair_scoped e1 e2 :
     expr_scoped n e1 →
     expr_scoped n e2 →
     expr_scoped n (Pair e1 e2)
 | Fst_scoped e :
     expr_scoped n e →
     expr_scoped n (Fst e)
 | Snd_scoped e :
     expr_scoped n e →
     expr_scoped n (Snd e)
 | InjL_scoped e :
     expr_scoped n e →
     expr_scoped n (InjL e)
 | InjR_scoped e :
     expr_scoped n e →
     expr_scoped n (InjR e)
 | Case_scoped e0 e1 e2 :
     expr_scoped n e0 →
     expr_scoped (S n) e1 →
     expr_scoped (S n) e2 →
     expr_scoped n (Case e0 e1 e2)
 | Fold_scoped e :
     expr_scoped n e →
     expr_scoped n (Fold e)
 | Unfold_scoped e :
     expr_scoped n e →
     expr_scoped n (Unfold e).

Lemma expr_Closed_n (e : expr) : ∀ n, Closed_n n e <-> expr_scoped n e.
Proof.
  induction e;
    (split;
     [ intro P; (try econstructor);
       try ((match goal with
            | H : ∀ n : nat, Closed_n n _ ↔ expr_scoped n _ |- _ => apply H
            end);
       closed_solver)
     | intro P; inversion P; intro σ; asimpl;
       repeat (match goal with
            | H : ∀ n : nat, Closed_n n _ ↔ expr_scoped n _ |- _ => rewrite (iffRL (H _) _)
            end);
       try done
    ]).
  - by apply Var_closed_n_lt.
  - by rewrite upn_lt.
Qed.

Lemma expr_typed_scoped Γ (e : expr) τ : typed Γ e τ → expr_scoped (length Γ) e.
Proof. intro de. apply expr_Closed_n. intro σ. by eapply typed_n_closed. Qed.

From st.lam Require Import contexts.

Inductive ctx_item_scoped : ctx_item → nat → nat → Prop :=
  | CTX_Lam_scoped n :
      ctx_item_scoped CTX_Lam (S n) n
  | CTX_AppL_scoped n e2 :
      expr_scoped n e2 →
      ctx_item_scoped (CTX_AppL e2) n n
  | CTX_AppR_scoped n e1 :
      expr_scoped n e1 →
      ctx_item_scoped (CTX_AppR e1) n n
  | CTX_LetInL_scoped n e2 :
      expr_scoped (S n) e2 →
      ctx_item_scoped (CTX_LetInL e2) n n
  | CTX_LetInR_scoped n e1 :
      expr_scoped n e1 →
      ctx_item_scoped (CTX_LetInR e1) (S n) n
  | CTX_PairL_scoped n e2:
      expr_scoped n e2 →
      ctx_item_scoped (CTX_PairL e2) n n
  | CTX_PairR_scoped n e1 :
      expr_scoped n e1 →
      ctx_item_scoped (CTX_PairR e1) n n
  | CTX_Fst_scoped n :
      ctx_item_scoped (CTX_Fst) n n
  | CTX_Snd_scoped n :
      ctx_item_scoped (CTX_Snd) n n
  | CTX_InjL_scoped n :
      ctx_item_scoped (CTX_InjL) n n
  | CTX_InjR_scoped n :
      ctx_item_scoped (CTX_InjR) n n
  | CTX_CaseL_scoped n e1 e2 :
      expr_scoped (S n) e1 →
      expr_scoped (S n) e2 →
      ctx_item_scoped (CTX_CaseL e1 e2) n n
  | CTX_CaseM_scoped n e0 e2 :
      expr_scoped n e0 →
      expr_scoped (S n) e2 →
      ctx_item_scoped (CTX_CaseM e0 e2) (S n) n
  | CTX_CaseR_scoped n e0 e1 :
      expr_scoped n e0 →
      expr_scoped (S n) e1 →
      ctx_item_scoped (CTX_CaseR e0 e1) (S n) n
  | CTX_BinOpL_scoped n op e2 :
      expr_scoped n e2 →
      ctx_item_scoped (CTX_BinOpL op e2) n n
  | CTX_BinOpR_scoped n op e1 :
      expr_scoped n e1 →
      ctx_item_scoped (CTX_BinOpR op e1) n n
  | CTX_IfL_scoped n e1 e2 :
      expr_scoped n e1 →
      expr_scoped n e2 →
      ctx_item_scoped (CTX_IfL e1 e2) n n
  | CTX_IfM_scoped n e0 e2 :
      expr_scoped n e0 →
      expr_scoped n e2 →
      ctx_item_scoped (CTX_IfM e0 e2) n n
  | CTX_IfR_scoped n e0 e1 :
      expr_scoped n e0 →
      expr_scoped n e1 →
      ctx_item_scoped (CTX_IfR e0 e1) n n
  | CTX_Fold_scoped n :
      ctx_item_scoped CTX_Fold n n
  | CTX_Unfold_scoped n :
      ctx_item_scoped CTX_Unfold n n.

Notation "|s> n ⊢ₙₒ e" := (expr_scoped n e) (at level 74, n, e at next level).
Notation "|sCi> n ⊢ₙₒ Ci ☾ m ☽" := (ctx_item_scoped Ci m n) (at level 74, n, Ci, m at next level).

Lemma ctx_item_typed_scoped Γ τ Γ' τ' (Ci : ctx_item) : typed_ctx_item Ci Γ τ Γ' τ' → ctx_item_scoped Ci (length Γ) (length Γ').
Proof.
  intro dCi. destruct dCi; constructor; try by eapply expr_typed_scoped.
  change (S (length Γ)) with (length (τ :: Γ)); by eapply expr_typed_scoped.
  change (S (length Γ)) with (length (τ1 :: Γ)); by eapply expr_typed_scoped.
  change (S (length Γ)) with (length (τ2 :: Γ)); by eapply expr_typed_scoped.
  change (S (length Γ)) with (length (τ2 :: Γ)); by eapply expr_typed_scoped.
  change (S (length Γ)) with (length (τ1 :: Γ)); by eapply expr_typed_scoped.
Qed.

Lemma scoped_ctx_item_typed n m C e :
  |s> m ⊢ₙₒ e →
  |sCi> n ⊢ₙₒ C ☾ m ☽ →
  |s> n ⊢ₙₒ (fill_ctx_item C e).
Proof.
  induction C; simpl; intros;
    (match goal with
     | H : |sCi> _ ⊢ₙₒ _ ☾ _ ☽ |- _ => inversion H
     end); simplify_eq; try by econstructor.
Qed.

Inductive ctx_scoped : ctx → nat → nat → Prop :=
  | CTX_nil_scoped n :
    ctx_scoped [] n n
  | CTX_cons_scoped n1 n2 n3 k K :
    ctx_item_scoped k n2 n3 →
    ctx_scoped K n1 n2 →
    ctx_scoped (k :: K) n1 n3.

Lemma ctx_typed_scoped Γ τ Γ' τ' (C : ctx) : typed_ctx C Γ τ Γ' τ' → ctx_scoped C (length Γ) (length Γ').
Proof.
  intro dC. induction dC; first constructor.
  simpl. econstructor. by eapply ctx_item_typed_scoped. auto.
Qed.

Notation "|sC> n ⊢ₙₒ C ☾ m ☽" := (ctx_scoped C m n) (at level 74, n, C, m at next level).
