From iris.program_logic Require Export language ectx_language ectxi_language.
From st.prelude Require Export autosubst generic lang_base.

(** The syntax of expressions *)
Inductive expr :=
| Var (x : var)
| LetIn (e1 : expr) (e2 : {bind 1 of expr})
| Lam (e : {bind 1 of expr})
(* | Fix (e : expr) *)
(* | Rec (e : {bind 2 of expr}) *)
| App (e1 e2 : expr)
(* Base Types *)
| Lit (l : base_lit)
| BinOp (op : bin_op) (e1 e2 : expr)
| If (e0 e1 e2 : expr)
| Seq (e1 e2 : expr)
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
(** Polymorphic Types *)
(* | TLam (e : expr) *)
(* | TApp (e : expr). *)
(* Virt Step *)
| VirtStep (e : expr).

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

Instance Var_Inj : Inj eq eq Var. intros x1 x2 eq. by inversion eq. Qed.

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Lemma Var_closed_n_lt (x : var) n (p : Closed_n n (Var x)) : x < n.
Proof. apply ids_lt_Closed_n. apply p. Qed.

(** Values for STLang *)
Inductive val :=
| LamV (e : {bind 1 of expr})
(* | RecV (e : {bind 2 of expr}) *)
(* | TLamV (e : {bind 1 of expr}) *)
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
 (* | RecV e => Rec e *)
 (* | TLamV e => TLam e *)
 | LitV v => Lit v
 | PairV v1 v2 => Pair (of_val v1) (of_val v2)
 | InjLV v => InjL (of_val v)
 | InjRV v => InjR (of_val v)
 | FoldV v => Fold (of_val v)
 end.

(* Notation "# v" := (of_val v%Vₙₒ) (at level 8, format "# v") : expr_no_st_scope. *)
Coercion of_val : val >-> expr.

Definition subst_list_val (vs : list val) : var → expr := subst_list (map of_val vs).

Lemma subst_list_val_cons v vs : of_val v .: subst_list_val vs = subst_list_val (v :: vs).
Proof. intros. by asimpl. Qed.

Lemma subst_list_val_snoc vs v : subst_list_val (vs ++ [v]) = (upn (length vs) (of_val v .: ids)) >> (subst_list_val vs).
Proof. by rewrite /subst_list_val map_app subst_list_snoc map_length. Qed.

(* Lemma var_subst_list_val_lt_length (vs : list val) (x : var) (p : x < length vs) : *)
(*   (exists v : val, vs !! x = Some v ∧ (Var x).[subst_list_val vs] = v). *)
(* Proof. *)
(*   destruct (vs !! x) eqn:eq. exists v. split; auto. apply ids_subst_list_lookup. by rewrite list_lookup_fmap eq /=. *)
(*   assert (length vs ≤ x). by apply lookup_ge_None. lia. *)
(* Qed. *)
Lemma Var_subst_list_closed_n_length (vs : list val) (x : var) (p : Closed_n (length vs) (Var x)) :
  (exists v : val, vs !! x = Some v ∧ (Var x).[subst_list_val vs] = v).
Proof.
  destruct (vs !! x) eqn:eq. exists v. split; auto. apply ids_subst_list_lookup. by rewrite list_lookup_fmap eq /=.
  assert (length vs ≤ x). by apply lookup_ge_None.
  assert (x < length vs). by apply ids_lt_Closed_n. lia.
Qed.

Lemma Var_subst_list_val_lookup (x : var) (ts : list val) t (H : ts !! x = Some t) :
  (ids x).[subst_list_val ts] = t.
Proof. rewrite /subst_list_val. apply ids_subst_list_lookup. by rewrite list_lookup_fmap H. Qed.

(* Lemma var_subst_list_val (vs : list val) (x : var) : *)
(*   (exists v : val, vs !! x = Some v ∧ (Var x).[subst_list_val vs] = v) ∨ (vs !! x = None). *)
(* Proof. *)
(*   destruct (vs !! x) eqn:eq. *)
(*   - left. exists v. split; auto. apply ids_subst_list_lookup. by rewrite list_lookup_fmap eq /=. *)
(*   - by right. *)
(* Qed. *)

Fixpoint to_val (e : expr) : option val :=
 match e with
 | Lam e => Some (LamV e)
 (* | Rec e => Some (RecV e) *)
 (* | TLam e => Some (TLamV e) *)
 | Lit e => Some (LitV e)
 | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
 | InjL e => InjLV <$> to_val e
 | InjR e => InjRV <$> to_val e
 | Fold e => v ← to_val e; Some (FoldV v)
 | _ => None
 end.

Fixpoint val_subst (v : val) (σ : var → expr) : val :=
  match v with
  | LamV e => LamV (e.[up σ])
  | LitV v => LitV v
  | PairV v1 v2 => PairV (val_subst v1 σ) (val_subst v2 σ)
  | InjLV v => InjLV (val_subst v σ)
  | InjRV v => InjRV (val_subst v σ)
  | FoldV v => FoldV (val_subst v σ)
  end.

Notation "v .{ sigma }" := (val_subst v sigma)
  (at level 2, sigma at level 200, left associativity,
   format "v .{ sigma }" ).

Notation "v .{ t /}" := (val_subst v (t .: ids))
  (at level 2, t at level 200, left associativity,
   format "v .{ t /}") : subst_scope.

Lemma val_subst_valid (v : val) (σ : var → expr) : (of_val v).[σ] = (val_subst v σ).
Proof. induction v; asimpl; try done; (by rewrite IHv1 IHv2) || by rewrite IHv. Qed.

Lemma val_subst_comp (v : val) (σ σ' : var → expr) : v.{σ}.{σ'} = v.{σ >> σ'}.
Proof. induction v; asimpl; try done; (by rewrite IHv1 IHv2) || by rewrite IHv. Qed.

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

Global Instance val_inhabited : Inhabited val := populate ()%Vₙₒ.
(* Instance expr_inhabited : Inhabited expr := populate (Lit LitUnit). *)
(* Instance val_inhabited : Inhabited val := populate (LitV LitUnit). *)
(* Canonical Structure stateC := leibnizO state. *)
(* Canonical Structure valC := leibnizO val. *)
(* Canonical Structure eff_valC := leibnizO eff_val. *)
(* Canonical Structure exprC := leibnizO expr. *)

(** Evaluation contexts *)
Inductive ectx_item :=
(* | FixCtx *)
| LetInCtx (e2 : expr)
| AppLCtx (e2 : expr)
| AppRCtx (v1 : val)
(* | TAppCtx *)
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
| SeqCtx (e2 : expr)
| FoldCtx
| UnfoldCtx
| VirtStepCtx.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
 match Ki with
 (* | FixCtx => Fix e *)
 | LetInCtx e2 => LetIn e e2
 | AppLCtx e2 => App e e2
 | AppRCtx v1 => App (of_val v1) e
 (* | TAppCtx => TApp e *)
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
 | SeqCtx e2 => Seq e e2
 | FoldCtx => Fold e
 | UnfoldCtx => Unfold e
 | VirtStepCtx => VirtStep e
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
  LetIn_head_step e1 v1 e2 σ :
   to_val e1 = Some v1 →
   head_step (LetIn e1 e2) σ [] e2.[e1/] σ []
| App_Lam_head_step e1 e2 v2 σ :
   to_val e2 = Some v2 →
   head_step (App (Lam e1) e2) σ [] e1.[e2/] σ []
(* | App_Rec_head_step e1 e2 v2 σ : *)
   (* to_val e2 = Some v2 → *)
   (* head_step (App (Rec e1) e2) σ [] e1.[(Rec e1), e2/] σ [] *)
(* fix *)
(* | Fix_head_step e σ : *)
    (* head_step (Fix (Lam e)) σ [] e.[Fix (Lam e)/] σ [] *)
(* binary operation *)
| BinOp_head_step op e1 e2 z1 z2 σ :
   to_val e1 = Some (LitV $ LitInt z1) → to_val e2 = Some (LitV $ LitInt z2) →
   head_step (BinOp op e1 e2) σ [] (of_val (bin_op_eval op z1 z2)) σ []
(* if *)
| If_True_head_step e1 e2 σ :
   head_step (If (Lit $ LitBool true) e1 e2) σ [] e1 σ []
| If_False_head_step e1 e2 σ :
   head_step (If (Lit $ LitBool false) e1 e2) σ [] e2 σ []
(* seq *)
| Seq_Unit_head_step e1 e2 σ :
    to_val e1 = Some ()%Vₙₒ →
    head_step (Seq e1 e2) σ [] e2 σ []
(* Products *)
| Fst_Pair_head_step e1 v1 e2 v2 σ :
   to_val e1 = Some v1 → to_val e2 = Some v2 →
   head_step (Fst (Pair e1 e2)) σ [] e1 σ []
| Snd_Pair_head_step e1 v1 e2 v2 σ :
   to_val e1 = Some v1 → to_val e2 = Some v2 →
   head_step (Snd (Pair e1 e2)) σ [] e2 σ []
(* Sums *)
| Case_InjL_head_step e0 v0 e1 e2 σ :
   to_val e0 = Some v0 →
   head_step (Case (InjL e0) e1 e2) σ [] e1.[e0/] σ []
| Case_InjR_head_step e0 v0 e1 e2 σ :
   to_val e0 = Some v0 →
   head_step (Case (InjR e0) e1 e2) σ [] e2.[e0/] σ []
(* Recursive Types *)
| Unfold_Fold_head_step e v σ :
   to_val e = Some v →
   head_step (Unfold (Fold e)) σ [] e σ []
(* Polymorphic Types *)
(* | TBeta e σ : *)
   (* head_step (TApp (TLam e)) σ [] e σ []. *)
| VirtStep_Lam_head_step e σ :
   head_step (VirtStep (Lam e)) σ [] (Lam (VirtStep ((Lam e).[ren (+1)] (VirtStep %0))))%Eₙₒ σ []
| VirtStep_Lit_head_step bl σ :
   head_step (VirtStep (Lit bl)) σ [] (Lit bl) σ []
| VirtStep_Pair_head_step e1 v1 e2 v2 σ :
   to_val e1 = Some v1 →
   to_val e2 = Some v2 →
   head_step (VirtStep (Pair e1 e2)) σ [] (Pair (VirtStep e1) (VirtStep e2)) σ []
| VirtStep_InjL_head_step e v σ :
   to_val e = Some v →
   head_step (VirtStep (InjL e)) σ [] (InjL (VirtStep e)) σ []
| VirtStep_InjR_head_step e v σ :
   to_val e = Some v →
   head_step (VirtStep (InjR e)) σ [] (InjR (VirtStep e)) σ []
| VirtStep_Fold_head_step e v σ :
   to_val e = Some v →
   head_step (VirtStep (Fold e)) σ [] (Fold (VirtStep e)) σ [].

Lemma App_Lam_head_step' (e' e1 e2 : expr) v2 (eq : e1.[e2/] = e') σ (H : to_val e2 = Some v2) :
  head_step (Lam e1 e2) σ [] e' σ [].
Proof. rewrite -eq. by eapply App_Lam_head_step. Qed.

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

Canonical Structure STLCmuVS_ectxi_lang : ectxiLanguage := EctxiLanguage st_ectxi_lang_mixin.
Canonical Structure STLCmuVS_ectx_lang : ectxLanguage := EctxLanguageOfEctxi STLCmuVS_ectxi_lang.
Canonical Structure STLCmuVS_lang : language := LanguageOfEctx STLCmuVS_ectx_lang.

Lemma fill_val (e : expr) (K : list ectx_item):
  is_Some (to_val (fill K e)) -> is_Some (to_val e).
Proof.
  move=> [v h]. destruct (to_val e) eqn:eq.
    by exists v0.
    have fill_not_val: to_val (fill K e) = None. eauto using fill_not_val.
    congruence.
Qed.

Canonical Structure valO := valO STLCmuVS_lang.
Canonical Structure exprO := exprO STLCmuVS_lang.

(* Arguments val_stuck {_ _ _ _ _} _. *)
(* Arguments fill_val {_ _} _. *)

(* Wrapper around prim_step *)

Definition STLCmuVS_step (e1 e2 : expr) : Prop := prim_step e1 tt [] e2 tt [].

(* We do not use forks, nor prophecy variables. *)

Lemma head_step_no_forks e σ κ e' σ' efs : head_step e σ κ e' σ' efs → efs = [].
Proof. intros H. by inversion H. Qed.

Lemma prim_step_no_forks (e : expr) σ κ e' σ' efs : prim_step e σ κ e' σ' efs → efs = [].
Proof. intros H. inversion H. by eapply head_step_no_forks. Qed.

Lemma head_step_no_obs e σ κ e' σ' efs : head_step e σ κ e' σ' efs → κ = [].
Proof. intros H. by inversion H. Qed.

Lemma prim_step_no_obs (e : expr) σ κ e' σ' efs : prim_step e σ κ e' σ' efs → κ = [].
Proof. intros H. inversion H. by eapply head_step_no_obs. Qed.

(* Our language is deterministic *)

Lemma head_step_det e e1 σ1 κ1 σ1' efs1 e2 σ2 κ2 σ2' efs2 : head_step e σ1 κ1 e1 σ1' efs1 → head_step e σ2 κ2 e2 σ2' efs2 → e1 = e2.
Proof. intros H1 H2. inversion H1; inversion H2; ((by simplify_eq) || (try done) || simplify_eq; inversion G2). Qed.

Lemma prim_step_det (e e1 e2 : expr) σ κ : prim_step e σ κ e1 σ [] → prim_step e σ κ e2 σ [] → e1 = e2.
Proof.
  intros H1 H2.
  inversion H1. inversion H2. simplify_eq. simpl in *.
  assert (K = K0) as <-.
  { destruct (step_by_val K K0 _ _ σ κ e2'0 σ [] H4) as [Kred eq] ; try done; try by eapply val_stuck.
    assert (H4' : fill K0 e1'0 = fill K e1'); first done.
    destruct (step_by_val K0 K _ _ σ κ e2' σ [] H4') as [Kred' eq'] ; try done; try by eapply val_stuck.
    rewrite eq in eq'. simpl in *. assert (length K = length (Kred' ++ Kred ++ K)). simpl in *. by rewrite -eq'.
    do 2 rewrite app_length in H. assert (Kred = []) as ->. apply length_zero_iff_nil. lia. by rewrite eq. }
  f_equal. assert (e1' = e1'0) as ->. apply (fill_inj K _ _ H4). by eapply head_step_det.
Qed.

(* Our language is pure *)

Lemma prim_step_pure (e1 e2 : expr) σ1 σ2 κ efs : prim_step e1 σ1 κ e2 σ2 efs → pure_step e1 e2.
Proof.
  intros Hprim.
  assert (efs = []) as ->. by eapply prim_step_no_forks.
  assert (κ = []) as ->. by eapply prim_step_no_obs.
  destruct σ1, σ2.
  split.
  intros σ. destruct σ. rewrite /reducible_no_obs. by exists e2, tt, [].
  intros.
  assert (efs = []) as ->. by eapply prim_step_no_forks.
  assert (κ = []) as ->. by eapply prim_step_no_obs.
  destruct σ1, σ2. by erewrite (prim_step_det _ _ _ _ _ H).
Qed.

(* Wrappers around lemmas *)

Lemma STLCmuVS_pure e1 e2 : STLCmuVS_step e1 e2 <-> pure_step e1 e2.
Proof.
  split. apply prim_step_pure. intro H. inversion H.
  destruct (pure_step_safe tt) as [e2' [σ [efs Hp]]].
  destruct σ. by destruct (pure_step_det _ _ _ _ _ Hp) as [a [b [-> ->]]].
Qed.

Lemma STLCmuVS_step_ctx K `{!LanguageCtx K} e1 e2 : STLCmuVS_step e1 e2 → STLCmuVS_step (K e1) (K e2).
Proof. intro. apply STLCmuVS_pure. apply pure_step_ctx. auto. by apply STLCmuVS_pure. Qed.

Lemma rtc_STLCmuVS_step_ctx K `{!LanguageCtx K} e1 e2 : rtc STLCmuVS_step e1 e2 → rtc STLCmuVS_step (K e1) (K e2).
Proof. eauto using rtc_congruence, STLCmuVS_step_ctx. Qed.

Lemma nsteps_STLCmuVS_step_ctx K `{!LanguageCtx K} n e1 e2 : nsteps STLCmuVS_step n e1 e2 → nsteps STLCmuVS_step n (K e1) (K e2).
Proof. eauto using nsteps_congruence, STLCmuVS_step_ctx. Qed.

Lemma nsteps_PureExec (e1 e2 : expr) n : nsteps STLCmuVS_step n e1 e2 <-> PureExec True n e1 e2.
Proof.
  split. intros s t. eapply nsteps_congruence with (f := id). by apply STLCmuVS_pure. auto.
  intro H. eapply nsteps_congruence with (f := id). apply STLCmuVS_pure. apply pure_exec. auto.
Qed.

Lemma rtc_PureExec (e1 e2 : expr) : rtc STLCmuVS_step e1 e2 <-> ∃ n, PureExec True n e1 e2.
Proof.
  split.
  intro H. assert (H' : rtc pure_step e1 e2).
  eapply rtc_subrel. by apply STLCmuVS_pure. auto. destruct (rtc_nsteps _ _ H') as [n H'']. exists n. intros _. done.
  intro d. destruct d as [n H]. eapply nsteps_rtc. by apply nsteps_PureExec.
Qed.

Lemma step_PureExec (e1 e2 : expr) : STLCmuVS_step e1 e2 → PureExec True 1 e1 e2.
Proof. intros s t. apply nsteps_once. by apply STLCmuVS_pure. Qed.

Definition STLCmuVS_halts (e : STLCmuVS.lang.expr) : Prop :=
  ∃ (v : STLCmuVS.lang.val), rtc STLCmuVS_step e (STLCmuVS.lang.of_val v).
