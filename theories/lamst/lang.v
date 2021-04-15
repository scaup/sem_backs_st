From iris.program_logic Require Import language ectx_language ectxi_language.
From st.prelude Require Export autosubst generic.
From stdpp Require Import gmap prelude.

Local Open Scope Z_scope.

(** Locations are defined as positive numbers *)
Definition loc := positive.

Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

(** The litterals of the language *)
Inductive base_lit : Set :=
| LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc).

Inductive bin_op : Set :=
| PlusOp | MinusOp | LeOp | LtOp | EqOp.

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
(* | TApp (e : expr) *)
(* Kleisli *)
| Return (e: expr)
| Bind (e1: expr) (e2: expr)
| RunST (e: expr)
(* Reference Types *)
| Alloc (e : expr)
| Read (e : expr)
| Write (e1 : expr) (e2 : expr)
| Compare (e1 : expr) (e2 : expr).

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

(** Values for STLang *)
Inductive val :=
| LamV (e : {bind 1 of expr})
(* | RecV (e : {bind 2 of expr}) *)
(* | TLamV (e : {bind 1 of expr}) *)
| ReturnV (v: val)
| BindV (v1 v2: val)
| LitV (v : base_lit)
| PairV (v1 v2 : val)
| InjLV (v : val)
| InjRV (v : val)
| FoldV (v : val)
| AllocV (v : val)
| ReadV (v : val)
| WriteV (v1 v2 : val).

Declare Scope val_st_scope.
Delimit Scope val_st_scope with Vₛₜ.

Notation "()" := (LitV LitUnit) : val_st_scope.

Fixpoint of_val (v : val) : expr :=
 match v with
 | LamV e => Lam e
 (* | RecV e => Rec e *)
 (* | TLamV e => TLam e *)
 | ReturnV v => Return (of_val v)
 | BindV v1 v2 => Bind (of_val v1) (of_val v2)
 | LitV v => Lit v
 | PairV v1 v2 => Pair (of_val v1) (of_val v2)
 | InjLV v => InjL (of_val v)
 | InjRV v => InjR (of_val v)
 | FoldV v => Fold (of_val v)
 | AllocV v => Alloc (of_val v)
 | ReadV v => Read (of_val v)
 | WriteV v v' => Write (of_val v) (of_val v')
 end.

Fixpoint to_val (e : expr) : option val :=
 match e with
 | Lam e => Some (LamV e)
 (* | Rec e => Some (RecV e) *)
 (* | TLam e => Some (TLamV e) *)
 | Return e => v ← to_val e; Some (ReturnV v)
 | Bind e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (BindV v1 v2)
 | Lit e => Some (LitV e)
 | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
 | InjL e => InjLV <$> to_val e
 | InjR e => InjRV <$> to_val e
 | Fold e => v ← to_val e; Some (FoldV v)
 | Alloc e => v ← to_val e; Some (AllocV v)
 | Read e => v ← to_val e; Some (ReadV v)
 | Write e e' => v ← to_val e; v' ← to_val e'; Some (WriteV v v')
 | _ => None
 end.

(** Contexts for the effectful language are of the form [Bind (Bind [] v2) v1] *)
Inductive eff_ectx_item := BindECtx (v : val).

(** A function that fills a context with an expression: *)
Definition eff_fill_item (Ki : eff_ectx_item) (e : expr) : expr :=
 match Ki with BindECtx v => Bind e (of_val v) end.

(** The state is defined as finite map from [loc] to [val]: *)
Definition state := gmap loc val.

(** Reduction relation for the effectful language *)
Inductive eff_head_step :
expr -> state -> list Empty_set → expr -> state → list expr → Prop :=
| ReadES l σ v :
   σ !! l = Some v ->
   eff_head_step (Read (Lit (LitLoc l))) σ [] (Return (of_val v)) σ []
| WriteES σ l e v :
   is_Some (σ !! l) -> to_val e = Some v ->
   eff_head_step (Write (Lit (LitLoc l)) e)
                  σ [] (Return (Lit LitUnit)) (<[l:=v]>σ) []
| AllocES σ l e v :
   (σ !! l) = None -> to_val e = Some v ->
   eff_head_step (Alloc e) σ [] (Return (Lit (LitLoc l))) (<[l:=v]>σ) []
| BindRetES σ v1 v2 e1 e2 :
   to_val e1 = Some v1 -> to_val e2 = Some v2 ->
   eff_head_step (Bind (Return e1) e2) σ [] (App e2 e1) σ [].

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
 by induction v; try simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
 revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

(** Values for the effectful language: *)
Inductive eff_val :=
| ReturnEV (v : val)
| AppCtxEV (K : list eff_ectx_item) (v1 v2 : val).

Definition of_eff_val (ev : eff_val) : expr :=
match ev with
| ReturnEV w => Return (of_val w)
| AppCtxEV K v1 v2 => fold_right eff_fill_item (App (of_val v1) (of_val v2)) K
end.

Instance maybe_AppCtxEV : Maybe3 AppCtxEV := λ ev,
 match ev with AppCtxEV K e1 e2 => Some (K, e1, e2) | _ => None end.

Fixpoint to_eff_val (e : expr) : option eff_val :=
 match e with
 | Return e => v ← to_val e; Some (ReturnEV v)
 | App e e' => v ← to_val e; v' ← to_val e'; Some (AppCtxEV [] v v')
 | Bind e e' => '(K, v1, v2) ← to_eff_val e ≫= maybe3 AppCtxEV; v' ← to_val e';
                 Some (AppCtxEV (BindECtx v' :: K) v1 v2)
 | _ => None
 end.

Lemma to_of_eff_val v : to_eff_val (of_eff_val v) = Some v.
Proof.
 destruct v as [|K v1 v2]; first by rewrite /= to_of_val.
 induction K as [|[]]; first rewrite /= !to_of_val //.
 rewrite /= IHK /= to_of_val //.
Qed.

Lemma of_to_eff_val e v : to_eff_val e = Some v → of_eff_val v = e.
  revert v. induction e => v; rewrite //=.
  - destruct (to_val e1) eqn:Heq1; rewrite //=;
    destruct (to_val e2) eqn:Heq2; rewrite //=.
    inversion 1; subst; simpl; erewrite !of_to_val; eauto.
 - destruct (to_val e) eqn:Heq1; rewrite //=.
   inversion 1; subst; simpl; erewrite !of_to_val; eauto.
 - destruct (to_eff_val e1) as [[]|] eqn:Heq1; rewrite //=.
   destruct (to_val e2) eqn:Heq2; rewrite //=. inversion 1; subst; simpl.
   specialize (IHe1 (AppCtxEV K _ _) eq_refl). simpl in *. rewrite IHe1.
   erewrite !of_to_val; eauto.
Qed.

(** Equality and other typeclass stuff *)
Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
Instance eff_of_val_inj : Inj (=) (=) of_eff_val.
Proof.
 intros v; induction v => w.
 - destruct w; simpl.
   + inversion 1; subst; f_equal; by apply of_val_inj.
   + destruct K as [|[]]; done.
 - revert v1 v2 w. induction K as [|[] K'] => v1 v2 w; (destruct w; first done).
   + destruct K as [|[] K]; inversion 1; f_equal; eauto using of_val_inj.
   + destruct K as [|[]]; first done.
     inversion 1 as [[Hb1 Hb2]].
     specialize (IHK' _ _ (AppCtxEV K _ _) Hb1). inversion IHK'; subst.
     erewrite of_val_inj; eauto.
Qed.

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
Instance eff_val_eq_dec : EqDecision eff_val.
Proof.
 refine (λ v v', cast_if (decide (of_eff_val v = of_eff_val v')));
   abstract naive_solver.
Defined.

Instance expr_inhabited : Inhabited expr := populate (Lit LitUnit).
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Canonical Structure stateC := leibnizO state.
Canonical Structure valC := leibnizO val.
Canonical Structure eff_valC := leibnizO eff_val.
Canonical Structure exprC := leibnizO expr.

Instance eff_fill_item_inj Ki : Inj (=) (=) (eff_fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.
Lemma eff_fill_item_val Ki e :
 is_Some (to_eff_val (eff_fill_item Ki e)) → is_Some (to_eff_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.
Lemma eff_val_stuck e1 σ1 κ e2 σ2 efs :
 eff_head_step e1 σ1 κ e2 σ2 efs → to_eff_val e1 = None.
Proof. destruct 1; try done. simpl; rewrite H H0; done. Qed.
Lemma eff_head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
 eff_head_step (eff_fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_eff_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; by eauto. Qed.
Lemma eff_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
 to_eff_val e1 = None → to_eff_val e2 = None →
 eff_fill_item Ki1 e1 = eff_fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
 destruct Ki1, Ki2; intros; try discriminate; simplify_eq/=;
  repeat match goal with
  | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
  end; auto.
Qed.

(** Both languages share the same syntax: *)
Definition eff_expr := expr.

(** We declare that the effectful language is a language to Iris by giving the
 expressions, values, contexts and operations and lemmas on those. *)

Lemma eff_ectxi_lang_mixin : EctxiLanguageMixin of_eff_val to_eff_val eff_fill_item eff_head_step.
  split; eauto using to_of_eff_val, of_to_eff_val,
  eff_val_stuck, eff_fill_item_val, eff_fill_item_no_val_inj,
  eff_head_ctx_step_val, eff_fill_item_inj.
Qed.

Canonical Structure eff_ectxi_lang : ectxiLanguage := EctxiLanguage eff_ectxi_lang_mixin.
Canonical Structure eff_ectx_lang : ectxLanguage := EctxLanguageOfEctxi eff_ectxi_lang.
Canonical Structure eff_lang : language := LanguageOfEctx eff_ectx_lang.

Lemma eff_fill_val K e :
 is_Some (to_eff_val (fill K e)) → is_Some (to_eff_val e).
Proof.
  apply fill_val.
Qed.

Lemma eff_head_step_val σ (e : eff_expr) κ σ' e' efs :
  prim_step e σ κ e' σ' efs → is_Some (to_val e).
Proof.
  intros Hps. eapply prim_step_ind; eauto.
  intros K; revert e σ e' σ' Hps.
  induction K as [|Ki K IHK] using rev_ind; intros e σ e' σ' Hps e1' e2' He He' Hps'.
  - inversion Hps' as []; subst; simpl; eauto;
    repeat match goal with
    | H : to_val _ = _ |- _ => rewrite H
    end; simpl; eauto.
 - destruct Ki. simpl; intros; subst. rewrite /= fill_app /= to_of_val /=.
   edestruct (IHK (ectx_language.fill K e1')) as [? Heq]; eauto.
   by apply Ectx_step'. simpl in *; rewrite Heq; eauto.
Qed.

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
| AllocCtx
| ReadCtx
| WriteLCtx (e2 : expr)
| WriteRCtx (v1 : val)
| ReturnCtx
| BindLCtx (e2: expr)
| BindRCtx (v1: val)
| RunSTCtx
| CompLCtx (e2 : expr)
| CompRCtx (v1 : val).

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
 | AllocCtx => Alloc e
 | ReadCtx => Read e
 | WriteLCtx e2 => Write e e2
 | WriteRCtx v1 => Write (of_val v1) e
 | ReturnCtx => Return e
 | BindLCtx e2 => Bind e e2
 | BindRCtx v1 => Bind (of_val v1) e
 | RunSTCtx => RunST e
 | CompLCtx e2 => Compare e e2
 | CompRCtx v1 => Compare (of_val v1) e
 end.

(** The stepping relation *)

Definition bin_op_eval (op : bin_op) (z1 z2 : Z) : val :=
 match op with
 | PlusOp => LitV $ LitInt (z1 + z2)
 | MinusOp => LitV $ LitInt (z1 - z2)
 | LeOp => LitV $ LitBool $ bool_decide (z1 ≤ z2)
 | LtOp => LitV $ LitBool $ bool_decide (z1 < z2)
 | EqOp => LitV $ LitBool $ bool_decide (z1 = z2)
 end.

(** Reduction relation for STLang: *)
Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
(* Embedding of the effectful language into STLang *)
| EffS σ σ' (e : eff_expr) e' :
   prim_step e σ [] e' σ' [] ->
   head_step (RunST e) σ [] (RunST e') σ' []
| RunRet σ e v :
    to_val e = Some v ->
    head_step (RunST (Return e)) σ [] e σ []
| Compare_suc σ l :
    head_step
      (Compare (Lit (LitLoc l)) (Lit (LitLoc l))) σ [] (Lit (LitBool true)) σ []
| Compare_fail σ l l' :
    l ≠ l' →
    head_step
      (Compare (Lit (LitLoc l)) (Lit (LitLoc l'))) σ [] (Lit (LitBool false)) σ []
(* β *)
| LetIn_head_step e1 v1 e2 σ :
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
    to_val e1 = Some ()%Vₛₜ →
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
   head_step (Unfold (Fold e)) σ [] e σ [].
(* Polymorphic Types *)
(* | TBeta e σ : *)
   (* head_step (TApp (TLam e)) σ [] e σ []. *)

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
  eauto using eff_head_step_val.
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

Lemma lamst_ectxi_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; eauto using to_of_val, of_to_val,
  val_stuck, fill_item_val, fill_item_no_val_inj,
 head_ctx_step_val, fill_item_inj.
Qed.

Canonical Structure lamst_ectxi_lang : ectxiLanguage := EctxiLanguage lamst_ectxi_lang_mixin.
Canonical Structure lamst_ectx_lang : ectxLanguage := EctxLanguageOfEctxi lamst_ectxi_lang.
Canonical Structure lamst_lang : language := LanguageOfEctx lamst_ectx_lang.

Lemma ST_step_no_spawn e1 e2 σ1 κ σ2 nt:
  @language.prim_step lamst_lang e1 σ1 κ e2 σ2 nt -> nt = [].
Proof.
  elim=> ? ? ? ? ? H. by elim: H.
Qed.

Lemma eff_step_no_spawn e1 e2 σ1 κ σ2 nt:
  @language.prim_step eff_lang e1 σ1 κ e2 σ2 nt -> nt = [].
Proof.
  elim=> ? ? ? ? ? H. by elim: H.
Qed.

Lemma fill_val (e : expr) (K : list ectx_item):
  is_Some (to_val (fill K e)) -> is_Some (to_val e).
Proof.
  move=> [v h]. destruct (to_val e) eqn:eq.
    by exists v0.
    have fill_not_val: to_val (fill K e) = None. eauto using fill_not_val.
    congruence.
Qed.

Arguments val_stuck {_ _ _ _ _} _.
Arguments eff_head_step_val {_ _ _ _ _} _.
Arguments eff_step_no_spawn {_ _ _ _ _} _.
Arguments ST_step_no_spawn {_ _ _ _ _} _.
Arguments fill_val {_ _} _.


(* Lemma step_runst_noval e σ1 κ e2 σ2 efs: *)
(*   to_eff_val e = None -> *)
(*   @language.prim_step ST_lang (RunST e) σ1 κ e2 σ2 efs -> *)
(*   reducible (e: eff_expr) σ1 -> *)
(*   ∃ e', e2 = RunST e' ∧ @language.prim_step eff_lang e σ1 κ e' σ2 efs. *)
(* Proof. *)
(*   intros enotval ps reduc. inversion ps; subst. *)
(*   revert e1' H e2' H1 ps. *)
(*   inversion reduc as [efs' [x H]]. destruct H as [σ' [efse Heffstep]]. *)
(*   have eval := eff_head_step_val _ Heffstep. *)
(*   destruct K; simpl in *; subst; intros; subst. *)
(*   - inversion H1; subst. *)
(*     + exists e'. split; auto. *)
(*     + simpl in *. rewrite H0 in enotval. discriminate. *)
(*   - destruct e0. inversion H. elim H2. discriminate_list K. *)
(*     have fill_val:= fill_val eval. *)
(*     have hhh := val_stuck H1. rewrite hhh /is_Some in fill_val. *)
(*     by destruct fill_val. *)
(* Qed. *)

(* Arguments step_runst_noval {_ _ _ _ _} _ _ _. *)

(* Lemma alloc_fresh e v σ κ : *)
(* 	let l := fresh (dom _ σ) in *)
(* 	to_val e = Some v → *)
(*         eff_head_step (Alloc e) σ κ (Return (Lit (LitLoc l))) (<[l:=v]>σ) []. *)
(* Proof. *)
(*   intros; apply: AllocES => //. *)
(*     by apply (not_elem_of_dom (D:=gset _)), is_fresh. *)
(* Qed. *)


(* (** Deterministic version of the languages. We don't register these as *)
(* instances/canonical structures to avoid confusion in resolutions. *) *)


(* Inductive det_eff_head_step : *)
(*   expr -> state -> expr -> state → list expr → Prop := *)
(* | det_ReadES l σ v : *)
(*     σ !! l = Some v -> *)
(*     det_eff_head_step (Read (Lit (LitLoc l))) σ (Return (of_val v)) σ [] *)
(* | det_WriteES σ l e v : *)
(*     is_Some (σ !! l) -> to_val e = Some v -> *)
(*     det_eff_head_step (Write (Lit (LitLoc l)) e) *)
(*                   σ (Return (Lit LitUnit)) (<[l:=v]>σ) [] *)
(* | det_AllocES σ e v : *)
(*     to_val e = Some v -> *)
(*     det_eff_head_step *)
(*       (Alloc e) σ *)
(*       (Return (Lit (LitLoc (fresh (dom _ σ))))) *)
(*       (<[(fresh (dom _ σ)):=v]>σ) [] *)
(* | det_BindRetES σ v1 v2 e1 e2 : *)
(*     to_val e1 = Some v1 -> to_val e2 = Some v2 -> *)
(*     det_eff_head_step (Bind (Return e1) e2) σ (App e2 e1) σ []. *)

(* Lemma det_eff_head_step_eff_head_step e σ e' σ' es' : *)
(*   det_eff_head_step e σ e' σ' es' → eff_head_step e σ e' σ' es'. *)
(* Proof. *)
(*   destruct 1; try econstructor; eauto. *)
(*   eapply @not_elem_of_dom with (D := gset positive); first typeclasses eauto. *)
(*   eapply is_fresh. *)
(* Qed. *)

(* Lemma det_eff_val_stuck e1 σ1 e2 σ2 efs : *)
(*  det_eff_head_step e1 σ1 e2 σ2 efs → to_eff_val e1 = None. *)
(* Proof. destruct 1; try done. simpl; rewrite H H0; done. Qed. *)

(* Lemma det_eff_head_ctx_step_val Ki e σ1 e2 σ2 efs : *)
(*  det_eff_head_step (eff_fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_eff_val e). *)
(* Proof. destruct Ki; inversion_clear 1; simplify_option_eq; by eauto. Qed. *)

(* Lemma det_eff_head_step_det e σ e' σ' es' e'' σ'' es'' : *)
(*   det_eff_head_step e σ e' σ' es' → det_eff_head_step e σ e'' σ'' es'' → *)
(*   e' = e'' ∧ σ' = σ'' ∧ es' = es''. *)
(* Proof. *)
(*   intros H1; intros H2; destruct H1; inversion H2; subst; *)
(*     match goal with *)
(*       H1 : ?A = _, H2 : ?A = _ |- _ => *)
(*         by (rewrite H1 in H2; clear H1; inversion H2; subst) *)
(*     end. *)
(* Qed. *)

(* Program Definition det_eff_ectxi_lang : *)
(*  EctxiLanguage expr eff_val eff_ectx_item state := {| *)
(*   ectxi_language.of_val := of_eff_val; *)
(*   ectxi_language.to_val := to_eff_val; *)
(*   ectxi_language.fill_item := eff_fill_item; *)
(*   ectxi_language.head_step := det_eff_head_step *)
(* |}. *)
(* Solve Obligations with eauto using to_of_eff_val, of_to_eff_val, *)
(*  det_eff_val_stuck, eff_fill_item_val, eff_fill_item_no_val_inj, *)
(*  det_eff_head_ctx_step_val. *)

(* Definition det_eff_ectx_lang : EctxLanguage _ _ _ _ := *)
(*   (@EctxLanguage_instance_0 _ _ _ _ det_eff_ectxi_lang). *)

(* Definition det_eff_lang : language := (@ectx_lang _ _ _ _ det_eff_ectx_lang). *)

(* Lemma det_eff_head_step_val σ (e : eff_expr) σ' e' efs : *)
(*   @language.prim_step det_eff_lang e σ e' σ' efs → is_Some (to_val e). *)
(* Proof. *)
(*  intros Hps. eapply (@prim_step_ind _ _ _ _ det_eff_ectx_lang); eauto. *)
(*  intros K; revert e σ e' σ' Hps. *)
(*  induction K as [|[]]; intros e σ e' σ' Hps e1' e2' He He' Hps'. *)
(*  - inversion Hps' as []; subst; simpl; eauto; *)
(*    repeat match goal with *)
(*    | H : to_val _ = _ |- _ => rewrite H *)
(*    end; simpl; eauto. *)
(*  - simpl; intros; subst. rewrite /= to_of_val /=. *)
(*    edestruct (IHK (ectx_language.fill K e1')) as [? Heq]; eauto. *)
(*    by apply (@Ectx_step' _ _ _ _ det_eff_ectx_lang). *)
(*    simpl in *; rewrite Heq; eauto. *)
(* Qed. *)

(* Lemma eff_prim_step_impl e σ e' σ' es : *)
(*   @language.prim_step det_eff_lang e σ e' σ' es → *)
(*   @language.prim_step eff_lang e σ e' σ' es. *)
(* Proof. *)
(*   destruct 1; subst. *)
(*   apply (@fill_step _ _ (@ectx_lang_ctx *)
(*               _ _ _ _ *)
(*               (@EctxLanguage_instance_0 _ _ _ _ eff_ectxi_lang) K)). *)
(*   apply head_prim_step. *)
(*   simpl in *. by apply det_eff_head_step_eff_head_step. *)
(* Qed. *)

(* Lemma det_eff_prim_step_det e σ e' σ' es' e'' σ'' es'' : *)
(*   @language.prim_step det_eff_lang e σ e' σ' es' → *)
(*   @language.prim_step det_eff_lang e σ e'' σ'' es'' → *)
(*   e' = e'' ∧ σ' = σ'' ∧ es' = es''. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   eapply (fun P => @prim_step_ind _ _ _ _ det_eff_ectx_lang _ _ _ _ _ _ P H1) *)
(*   => K e1 e2 Heq1 Heq2 Hstp; subst. *)
(*   apply fill_step_inv in H2; last eapply ectx_language.val_stuck; eauto. *)
(*   destruct H2 as [e2' [-> H2]]. *)
(*   eapply (fun P => @prim_step_ind _ _ _ _ det_eff_ectx_lang _ _ _ _ _ _ P H2) *)
(*   => K' e3 e4 Heq3 Heq4 Hstp'; subst. *)
(*   assert (K' = []). *)
(*   { destruct K' as [|k' K']; trivial; simpl in *. *)
(*     apply det_eff_head_ctx_step_val in Hstp. *)
(*     apply det_eff_val_stuck in Hstp'. *)
(*     apply (@ectxi_language.fill_val _ _ _ _ det_eff_ectxi_lang K') in Hstp. *)
(*     simpl in Hstp; rewrite Hstp' in Hstp; inversion Hstp; congruence. } *)
(*   subst; simpl in *. *)
(*   pose proof (det_eff_head_step_det _ _ _ _ _ _ _ _ Hstp Hstp'); firstorder. *)
(* Qed. *)

(* Lemma det_eff_no_prim_step_return e σ e' σ' es' : *)
(*   is_Some (to_val e) → *)
(*   @language.prim_step det_eff_lang (Return e) σ e' σ' es' → False. *)
(* Proof. *)
(*   intros Hnis Hps. *)
(*   eapply (fun P => @prim_step_ind _ _ _ _ det_eff_ectx_lang _ _ _ _ _ _ P Hps) *)
(*   => K e1 e2 Heq1 Heq2 Hstp; subst. *)
(*   apply ectx_language.val_stuck in Hstp; simpl in *. *)
(*   destruct K as [|[] K]; simpl in *; inversion Heq1; subst; simpl in *. *)
(*   destruct (to_val e); inversion Hnis; simpl in *; try congruence. *)
(* Qed. *)

(* Inductive det_head_step : expr → state → expr → state → list expr → Prop := *)
(* | det_EffS σ σ' (e : eff_expr) e': *)
(*     @language.prim_step det_eff_lang e σ e' σ' [] -> *)
(*     det_head_step (RunST e) σ (RunST e') σ' [] *)
(* | det_RunRet σ e v : *)
(*     to_val e = Some v -> *)
(*    det_head_step (RunST (Return e)) σ e σ [] *)
(* | det_Compare_suc σ l : *)
(*     det_head_step *)
(*       (Compare (Lit (LitLoc l)) (Lit (LitLoc l))) σ (Lit (LitBool true)) σ [] *)
(* | det_Compare_fail σ l l': *)
(*     l ≠ l' → *)
(*     det_head_step *)
(*       (Compare (Lit (LitLoc l)) (Lit (LitLoc l'))) σ (Lit (LitBool false)) σ [] *)
(* (* β *) *)
(* | det_BetaS e1 e2 v2 σ : *)
(*    to_val e2 = Some v2 → *)
(*    det_head_step (App (Rec e1) e2) σ e1.[(Rec e1), e2/] σ [] *)
(* (* binary operation *) *)
(* | det_BinOpS op e1 e2 z1 z2 σ : *)
(*    to_val e1 = Some (LitV $ LitInt z1) → to_val e2 = Some (LitV $ LitInt z2) → *)
(*    det_head_step (BinOp op e1 e2) σ (of_val (bin_op_eval op z1 z2)) σ [] *)
(* (* if *) *)
(* | det_IfTrueS e1 e2 σ : *)
(*    det_head_step (If (Lit $ LitBool true) e1 e2) σ e1 σ [] *)
(* | det_IfFalseS e1 e2 σ : *)
(*    det_head_step (If (Lit $ LitBool false) e1 e2) σ e2 σ [] *)
(* (* Products *) *)
(* | det_FstS e1 v1 e2 v2 σ : *)
(*    to_val e1 = Some v1 → to_val e2 = Some v2 → *)
(*    det_head_step (Fst (Pair e1 e2)) σ e1 σ [] *)
(* | det_SndS e1 v1 e2 v2 σ : *)
(*    to_val e1 = Some v1 → to_val e2 = Some v2 → *)
(*    det_head_step (Snd (Pair e1 e2)) σ e2 σ [] *)
(* (* Sums *) *)
(* | det_CaseLS e0 v0 e1 e2 σ : *)
(*    to_val e0 = Some v0 → *)
(*    det_head_step (Case (InjL e0) e1 e2) σ e1.[e0/] σ [] *)
(* | det_CaseRS e0 v0 e1 e2 σ : *)
(*    to_val e0 = Some v0 → *)
(*    det_head_step (Case (InjR e0) e1 e2) σ e2.[e0/] σ [] *)
(* (* Recursive Types *) *)
(* | det_Unfold_Fold e v σ : *)
(*    to_val e = Some v → *)
(*    det_head_step (Unfold (Fold e)) σ e σ [] *)
(* (* Polymorphic Types *) *)
(* | det_TBeta e σ : *)
(*     det_head_step (TApp (TLam e)) σ e σ []. *)

(* Lemma det_head_step_head_step e σ e' σ' es' : *)
(*   det_head_step e σ e' σ' es' → head_step e σ e' σ' es'. *)
(* Proof. *)
(*   destruct 1; try econstructor; eauto using eff_prim_step_impl. *)
(* Qed. *)

(* Lemma det_val_stuck e1 σ1 e2 σ2 efs : *)
(*  det_head_step e1 σ1 e2 σ2 efs → to_val e1 = None. *)
(* Proof. destruct 1; done. Qed. *)
(* Lemma det_head_ctx_step_val Ki e σ1 e2 σ2 efs : *)
(*  det_head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e). *)
(* Proof. *)
(*  destruct Ki; inversion_clear 1; simplify_option_eq; *)
(*   eauto using det_eff_head_step_val. *)
(* Qed. *)

(* Lemma det_head_step_det e σ e' σ' es' e'' σ'' es'' : *)
(*   det_head_step e σ e' σ' es' → det_head_step e σ e'' σ'' es'' → *)
(*   e' = e'' ∧ σ' = σ'' ∧ es' = es''. *)
(* Proof. *)
(*   intros H1; intros H2; destruct H1; *)
(*     inversion H2; subst; auto; *)
(*       repeat match goal with *)
(*                H1 : ?A = _, H2 : ?A = _ |- _ => *)
(*                rewrite H1 in H2; clear H1; inversion H2; subst *)
(*              end; auto. *)
(*   - pose proof (det_eff_prim_step_det _ _ _ _ _ _ _ _ H H1); firstorder. *)
(*   - exfalso; eapply det_eff_no_prim_step_return; eauto. *)
(*   - exfalso; eapply det_eff_no_prim_step_return; eauto. *)
(*   - match goal with H : ?A ≠ ?A |- _ => by contradict H end. *)
(*   - match goal with H : ?A ≠ ?A |- _ => by contradict H end. *)
(* Qed. *)

(* Program Definition det_ectxi_lang : *)
(*  EctxiLanguage expr val ectx_item state := {| *)
(*   ectxi_language.of_val := of_val; *)
(*   ectxi_language.to_val := to_val; *)
(*   ectxi_language.fill_item := fill_item; *)
(*   ectxi_language.head_step := det_head_step *)
(* |}. *)
(* Solve Obligations with eauto using to_of_val, of_to_val, *)
(*  det_val_stuck, fill_item_val, fill_item_no_val_inj, *)
(*  det_head_ctx_step_val. *)

(* Definition det_ectx_lang : EctxLanguage _ _ _ _ := *)
(*   (@EctxLanguage_instance_0 _ _ _ _ det_ectxi_lang). *)

(* Definition det_lang : language := (@ectx_lang _ _ _ _ det_ectx_lang). *)

(* Lemma prim_step_impl e σ e' σ' es : *)
(*   @language.prim_step det_lang e σ e' σ' es → *)
(*   @language.prim_step ST_lang e σ e' σ' es. *)
(* Proof. *)
(*   destruct 1; subst. *)
(*   apply (@fill_step _ _ (@ectx_lang_ctx *)
(*               _ _ _ _ *)
(*               (@EctxLanguage_instance_0 _ _ _ _ ST_ectxi_lang) K)). *)
(*   apply head_prim_step. *)
(*   simpl in *. by apply det_head_step_head_step. *)
(* Qed. *)
