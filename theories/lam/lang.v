From iris.program_logic Require Export language ectx_language ectxi_language.
From st Require Export prelude.autosubst.
From stdpp Require Export prelude.

(* Local Open Scope Z_scope. *)

(** The litterals of the language *)
Inductive base_lit : Set :=
| LitInt (n : Z) | LitBool (b : bool) | LitUnit.

Inductive bin_op : Set :=
| PlusOp | MinusOp | LeOp | LtOp | EqOp.

(** The syntax of expressions *)
Inductive expr :=
| Var (x : var)
| LetIn (e : expr) (e : {bind 1 of expr})
| Lam (e : {bind 1 of expr})
| Rec (e : {bind 2 of expr})
| App (e1 e2 : expr)
(* Base Types *)
| Lit (l : base_lit)
| BinOp (op : bin_op) (e1 e2 : expr)
| If (e0 e1 e2 : expr)
(* Products *)
| Pair (e1 e2 : expr)
| Fst (e : expr)
| Snd (e : expr)
(* Sums *)
| InjL (e : expr)
| InjR (e : expr)
| Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
(* Recursive Types *)
| Fold (e : expr)
| Unfold (e : expr)
(* Polymorphic Types *)
| TLam (e : expr)
| TApp (e : expr).

Coercion LitInt : Z >-> base_lit.
Coercion LitBool : bool >-> base_lit.
Coercion Lit : base_lit >-> expr.
Coercion App : expr >-> Funclass.
Coercion Var : var >-> expr.

Declare Scope expr_no_st_scope.
Delimit Scope expr_no_st_scope with Eₙₒ.
Notation "% x" := (Var x%nat) (at level 8, format "% x") : expr_no_st_scope.

Notation "()" := (Lit LitUnit) : expr_no_st_scope.
Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1 e2) .. en) : expr_no_st_scope.

Notation "e1 + e2" := (BinOp PlusOp e1%Eₙₒ e2%Eₙₒ) : expr_no_st_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%Eₙₒ e2%Eₙₒ) : expr_no_st_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%Eₙₒ e2%Eₙₒ) : expr_no_st_scope.
Notation "e1 < e2" := (BinOp LtOp e1%Eₙₒ e2%Eₙₒ) : expr_no_st_scope.
Notation "e1 = e2" := (BinOp EqOp e1%Eₙₒ e2%Eₙₒ) : expr_no_st_scope.

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

(** Values for STLang *)
Inductive val :=
| LamV (e : {bind 1 of expr})
| RecV (e : {bind 1 of expr})
| TLamV (e : {bind 1 of expr})
| LitV (v : base_lit)
| PairV (v1 v2 : val)
| InjLV (v : val)
| InjRV (v : val)
| FoldV (v : val).

Coercion LitV : base_lit >-> val.

Declare Scope val_no_st_scope.
Delimit Scope val_no_st_scope with Vₙₒ.

Notation "()" := (LitV LitUnit) : val_no_st_scope.
Notation "( v1 , v2 , .. , vn )" := (PairV .. (PairV v1 v2) .. vn) : val_no_st_scope.

Fixpoint of_val (v : val) : expr :=
 match v with
 | LamV e => Lam e
 | RecV e => Rec e
 | TLamV e => TLam e
 | LitV v => Lit v
 | PairV v1 v2 => Pair (of_val v1) (of_val v2)
 | InjLV v => InjL (of_val v)
 | InjRV v => InjR (of_val v)
 | FoldV v => Fold (of_val v)
 end.

Fixpoint to_val (e : expr) : option val :=
 match e with
 | Lam e => Some (LamV e)
 | Rec e => Some (RecV e)
 | TLam e => Some (TLamV e)
 | Lit e => Some (LitV e)
 | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
 | InjL e => InjLV <$> to_val e
 | InjR e => InjRV <$> to_val e
 | Fold e => v ← to_val e; Some (FoldV v)
 | _ => None
 end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
 by induction v; try simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
 revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

(** Equality and other typeclass stuff *)
Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Instance expr_eq_dec : EqDecision expr.
Proof. solve_decision. Defined.
Instance val_eq_dec : EqDecision val.
Proof.
 refine (λ v v', cast_if (decide (of_val v = of_val v')));
   abstract naive_solver.
Defined.

Instance expr_inhabited : Inhabited expr := populate (Lit LitUnit).
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
(* Canonical Structure stateC := leibnizO state. *)
(* Canonical Structure valC := leibnizO val. *)
(* Canonical Structure eff_valC := leibnizO eff_val. *)
(* Canonical Structure exprC := leibnizO expr. *)

(** Evaluation contexts *)
Inductive ectx_item :=
| LetInLCtx (e2 : expr)
| LetInRCtx (v1 : val)
| AppLCtx (e2 : expr)
| AppRCtx (v1 : val)
| TAppCtx
| PairLCtx (e2 : expr)
| PairRCtx (v1 : val)
| FstCtx
| SndCtx
| InjLCtx
| InjRCtx
| CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
| IfCtx (e2 : expr) (e3 : expr)
| BinOpLCtx (op : bin_op) (e2 : expr)
| BinOpRCtx (op : bin_op) (v1 : val)
| FoldCtx
| UnfoldCtx.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
 match Ki with
 | LetInLCtx e2 => LetIn e e2
 | LetInRCtx v1 => LetIn (of_val v1) e
 | AppLCtx e2 => App e e2
 | AppRCtx v1 => App (of_val v1) e
 | TAppCtx => TApp e
 | PairLCtx e2 => Pair e e2
 | PairRCtx v1 => Pair (of_val v1) e
 | FstCtx => Fst e
 | SndCtx => Snd e
 | InjLCtx => InjL e
 | InjRCtx => InjR e
 | CaseCtx e1 e2 => Case e e1 e2
 | IfCtx e1 e2 => If e e1 e2
 | BinOpLCtx op e2 => BinOp op e e2
 | BinOpRCtx op v1 => BinOp op (of_val v1) e
 | FoldCtx => Fold e
 | UnfoldCtx => Unfold e
 end.

(** The stepping relation *)

Definition bin_op_eval (op : bin_op) (z1 z2 : Z) : val :=
 match op with
 | PlusOp => LitV $ LitInt (z1 + z2)%Z
 | MinusOp => LitV $ LitInt (z1 - z2)
 | LeOp => LitV $ LitBool $ bool_decide (z1 ≤ z2)%Z
 | LtOp => LitV $ LitBool $ bool_decide (z1 < z2)%Z
 | EqOp => LitV $ LitBool $ bool_decide (z1 = z2)
 end.

Definition state : Type := ().

Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
(* β *)
  BetaLetIn e1 v1 e2 v2 σ κ :
   to_val e1 = Some v1 →
   to_val e2 = Some v2 →
   head_step (LetIn e1 e2) σ κ e2.[e1/] σ []
| BetaLam e1 e2 v2 σ κ :
   to_val e2 = Some v2 →
   head_step (App (Lam e1) e2) σ κ e1.[e2/] σ []
| BetaS e1 e2 v2 σ κ :
   to_val e2 = Some v2 →
   head_step (App (Rec e1) e2) σ κ e1.[(Rec e1), e2/] σ []
(* binary operation *)
| BinOpS op e1 e2 z1 z2 σ κ :
   to_val e1 = Some (LitV $ LitInt z1) → to_val e2 = Some (LitV $ LitInt z2) →
   head_step (BinOp op e1 e2) σ κ (of_val (bin_op_eval op z1 z2)) σ []
(* if *)
| IfTrueS e1 e2 σ κ :
   head_step (If (Lit $ LitBool true) e1 e2) σ κ e1 σ []
| IfFalseS e1 e2 σ κ :
   head_step (If (Lit $ LitBool false) e1 e2) σ κ e2 σ []
(* Products *)
| FstS e1 v1 e2 v2 σ κ :
   to_val e1 = Some v1 → to_val e2 = Some v2 →
   head_step (Fst (Pair e1 e2)) σ κ e1 σ []
| SndS e1 v1 e2 v2 σ κ :
   to_val e1 = Some v1 → to_val e2 = Some v2 →
   head_step (Snd (Pair e1 e2)) σ κ e2 σ []
(* Sums *)
| CaseLS e0 v0 e1 e2 σ κ :
   to_val e0 = Some v0 →
   head_step (Case (InjL e0) e1 e2) σ κ e1.[e0/] σ []
| CaseRS e0 v0 e1 e2 σ κ :
   to_val e0 = Some v0 →
   head_step (Case (InjR e0) e1 e2) σ κ e2.[e0/] σ []
(* Recursive Types *)
| Unfold_Fold e v σ κ :
   to_val e = Some v →
   head_step (Unfold (Fold e)) σ κ e σ []
(* Polymorphic Types *)
| TBeta e σ κ :
   head_step (TApp (TLam e)) σ κ e σ [].

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.
Lemma fill_item_val Ki e :
 is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.
Lemma val_stuck e1 σ1 κ e2 σ2 efs :
 head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; done. Qed.
Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
 head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof.
 destruct Ki; inversion_clear 1; simplify_option_eq; eauto.
Qed.
Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
 to_val e1 = None → to_val e2 = None →
 fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
 destruct Ki1, Ki2; intros; try discriminate; simplify_eq/=;
  repeat match goal with
  | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
  end; auto.
Qed.

Lemma st_ectxi_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; eauto using to_of_val, of_to_val,
  val_stuck, fill_item_val, fill_item_no_val_inj,
 head_ctx_step_val, fill_item_inj.
Qed.

Canonical Structure lam_ectxi_lang : ectxiLanguage := EctxiLanguage st_ectxi_lang_mixin.
Canonical Structure lam_ectx_lang : ectxLanguage := EctxLanguageOfEctxi lam_ectxi_lang.
Canonical Structure lam_lang : language := LanguageOfEctx lam_ectx_lang.

Lemma fill_val (e : expr) (K : list ectx_item):
  is_Some (to_val (fill K e)) -> is_Some (to_val e).
Proof.
  move=> [v h]. destruct (to_val e) eqn:eq.
    by exists v0.
    have fill_not_val: to_val (fill K e) = None. eauto using fill_not_val.
    congruence.
Qed.

Arguments val_stuck {_ _ _ _ _} _.
Arguments fill_val {_ _} _.
