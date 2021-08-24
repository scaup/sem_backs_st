From st.STLCmuVS Require Import lang.
From st.STLCmu Require Import lang typing types contexts boring.
From st.STLCmuST Require Import lang types typing contexts.
From st.embedding Require Import types typed contexts.
From st.thms Require Import refl_ctx_equiv pres_ctx_equiv.
From st.end_to_end Require Import embedding_STLCmu_STLCmuST pres_ctx_equiv.
From st.backtranslations.st_sem Require retraction correctness.sem_le_st.logrel.definition correctness.st_le_sem.logrel.definition.

(* easy to believe helper lemmas to prove reflection *)
(* ------------------------------------------------- *)

Lemma embd_expr_halts_iff e (de : STLCmu.typing.typed [] e STLCmu.types.TUnit) :
  STLCmu_halts e <-> STLCmuST_halts [[e]].
Proof.
  apply (@iff_trans _ (STLCmuVS_halts (boring.embd_expr e)) _).
  - apply (boring.embd_expr_halts_iff e _ _ de).
  - rewrite -comp_embeddings. split.
    + apply sem_le_st.logrel.adequacy.exprel_adequate.
      intros Σ sem_le_stΣ.
      rewrite -(st_sem.retraction.retraction [] (boring.embd_expr e) STLCmu.types.TUnit).
      rewrite -> (st_sem.retraction.retraction [] (boring.embd_expr e) STLCmu.types.TUnit) at 1.
      apply correctness.sem_le_st.logrel.definition.open_exprel_typed_nil'.
      apply (sem_le_st.logrel.fundamental.fundamental [] (expressions.embd_expr (boring.embd_expr e))).
      change [] with (embed <$> []). change TUnit with (embed STLCmu.types.TUnit). apply embd_typed.
      all: by apply boring.embd_expr_typed.
    + apply st_le_sem.logrel.adequacy.exprel_adequate.
      intros Σ st_le_semΣ.
      rewrite <- (st_sem.retraction.retraction [] (boring.embd_expr e) STLCmu.types.TUnit) at 1.
      apply correctness.st_le_sem.logrel.definition.open_exprel_typed_nil'.
      apply (st_le_sem.logrel.fundamental.fundamental [] (expressions.embd_expr (boring.embd_expr e))).
      change [] with (embed <$> []). change TUnit with (embed STLCmu.types.TUnit). apply embd_typed.
      all: by apply boring.embd_expr_typed.
Qed.

Lemma comm_fill_ctx_item_embd (Ci : STLCmu.contexts.ctx_item) (e : STLCmu.lang.expr) :
  STLCmuST.contexts.fill_ctx_item (embd_ctx_item Ci) (embd_expr e) =
  embd_expr (STLCmu.contexts.fill_ctx_item Ci e).
Proof. by destruct Ci; simpl. Qed.

Lemma comm_fill_ctx_embd (C : STLCmu.contexts.ctx) (e : STLCmu.lang.expr) :
  STLCmuST.contexts.fill_ctx (embd_ctx C) (embd_expr e) =
  embd_expr (STLCmu.contexts.fill_ctx C e).
Proof.
  induction C; simpl; first done.
  by rewrite IHC comm_fill_ctx_item_embd.
Qed.

Fixpoint back_type (τ : STLCmuST.types.type) : STLCmu.types.type :=
  match τ with
  | TUnit => STLCmu.types.TUnit
  | TBool => STLCmu.types.TBool
  | TInt => STLCmu.types.TInt
  | TProd x x0 => STLCmu.types.TProd (back_type x) (back_type x0)
  | TSum x x0 => STLCmu.types.TSum (back_type x) (back_type x0)
  | TArrow x x0 => STLCmu.types.TArrow (back_type x) (back_type x0)
  | TRec τ => STLCmu.types.TRec (back_type τ)
  | TVar X => STLCmu.types.TVar X
  | TSTref ρ τ => STLCmu.types.TUnit
  | TST ρ τ => STLCmu.types.TUnit
  end.

Notation "<< τ >>" := (back_type τ) (at level 4, τ at next level).

Lemma back_type_ren_gen τ :
  forall k l, << τ.[upn l (ren (+k))] >> = <<τ>>.[upn l (ren (+k))].
Proof.
  induction τ; intros k l; try by asimpl.
  - asimpl. by rewrite IHτ1 IHτ2.
  - asimpl. by rewrite IHτ1 IHτ2.
  - asimpl. by rewrite IHτ1 IHτ2.
  - simpl. specialize (IHτ k (S l)). by rewrite IHτ.
  - asimpl. do 2 rewrite (iter_up l X (ren (+k))).
    destruct (lt_dec X l); by asimpl.
Qed.

Lemma back_TRec_comm_gen (τb : STLCmuST.types.type) : forall (τ : STLCmuST.types.type) k,
  << τb.[upn k (τ .: ids)] >> = <<τb>>.[upn k (<<τ>> .: ids)].
Proof.
  induction τb; intros τ' k; try by asimpl.
  - asimpl. by rewrite IHτb1 IHτb2.
  - asimpl. by rewrite IHτb1 IHτb2.
  - asimpl. by rewrite IHτb1 IHτb2.
  - simpl. specialize (IHτb τ' (S k)). by rewrite IHτb.
  - asimpl.
    rewrite (iter_up k X (τ' .: ids)) (iter_up k X (<<τ'>> .: ids)).
    destruct (lt_dec X k).
      + by asimpl.
      + destruct (decide (X - k = 0)); asimpl. rewrite e. asimpl.
        cut (<< τ'.[upn 0 (ren (+k))] >> = (<< τ' >>).[upn 0 (ren (+k))]).
        by asimpl. by rewrite back_type_ren_gen.
        destruct (X - k). exfalso; lia. by asimpl.
Qed.

Lemma back_TRec_comm (τb : STLCmuST.types.type) :
  << τb.[STLCmuST.types.TRec τb/]>> = <<τb>>.[STLCmu.types.TRec <<τb>>/].
Proof.
  cut (<< (τb.[upn 0 ((STLCmuST.types.TRec τb) .: ids)])>> = <<τb>>.[upn 0 (<<(STLCmuST.types.TRec τb)>> .: ids)]).
  by asimpl. apply back_TRec_comm_gen.
Qed.

From st.STLCmu Require Import typing.

Lemma embd_expr_typed_inv' e :
  ∀ Γ τ, STLCmuST.typing.typed Γ [[e]] τ →
  STLCmu.typing.typed (back_type <$> Γ) e (back_type τ).
Proof.
  induction e; simpl; intros Γ τ de; (try destruct l); inversion de; subst; (try by constructor).
  - constructor. by rewrite list_lookup_fmap H0 /=.
  - apply LetIn_typed with (τ1 := back_type τ1).
    rewrite -fmap_cons. by apply IHe0. by apply IHe.
  - constructor. rewrite -fmap_cons. by apply IHe.
  - apply App_typed with (τ1 := back_type τ1). specialize (IHe1 Γ (TArrow τ1 τ)).
    by apply IHe1. by apply IHe2.
  - specialize (IHe1 Γ TInt). specialize (IHe2 Γ TInt).
    destruct op; constructor; (try by apply IHe1); (try by apply IHe2).
  - constructor. by apply (IHe1 Γ TBool). by apply IHe2. by apply IHe3.
  - constructor. by apply (IHe1 Γ TUnit). by apply IHe2.
  - constructor. by apply IHe1. by apply IHe2.
  - econstructor. by apply (IHe Γ (TProd τ τ2)).
  - econstructor. by apply (IHe Γ (TProd τ1 τ)).
  - econstructor. by apply IHe.
  - econstructor. by apply IHe.
  - econstructor. by apply (IHe Γ (TSum τ1 τ2)).
    rewrite -fmap_cons; by apply IHe0.
    rewrite -fmap_cons; by apply IHe1.
  - econstructor. fold back_type. rewrite -back_TRec_comm. by apply IHe.
  - rewrite back_TRec_comm. econstructor. by apply (IHe Γ (TRec τ0)).
Qed.

Lemma embed_type_back_type τ : back_type (embed τ) = τ.
Proof. induction τ; simpl; try done; repeat f_equiv; try done. Qed.

Lemma embd_expr_typed_inv e :
  ∀ Γ τ, STLCmuST.typing.typed (embed <$> Γ) [[e]] (embed τ) →
  STLCmu.typing.typed Γ e τ.
Proof.
  intros Γ τ de. rewrite -(embed_type_back_type τ).
  rewrite -(list_fmap_id Γ) (list_fmap_ext id (back_type ∘ embed) Γ Γ); auto.
  rewrite list_fmap_compose. by apply embd_expr_typed_inv'.
  intros. by rewrite /= embed_type_back_type.
Qed.

Instance TVar_Inj : Inj eq eq TVar. intros x1 x2 eq. by inversion eq. Qed.

Lemma embed_Closed_n_inv τ : ∀ n, Closed_n n (embed τ) → Closed_n n τ.
Proof.
  induction τ; intros n pCn; try by intros σ; asimpl.
  - intro σ. asimpl. f_equiv.
    apply IHτ1. intro σ'. specialize (pCn σ'). asimpl in pCn. by simplify_eq.
    apply IHτ2. intro σ'. specialize (pCn σ'). asimpl in pCn. by simplify_eq.
  - intro σ. asimpl. f_equiv.
    apply IHτ1. intro σ'. specialize (pCn σ'). asimpl in pCn. by simplify_eq.
    apply IHτ2. intro σ'. specialize (pCn σ'). asimpl in pCn. by simplify_eq.
  - intro σ. asimpl. f_equiv.
    apply IHτ1. intro σ'. specialize (pCn σ'). asimpl in pCn. by simplify_eq.
    apply IHτ2. intro σ'. specialize (pCn σ'). asimpl in pCn. by simplify_eq.
  - intros σ. specialize (IHτ (S n)).
    asimpl. f_equiv. apply IHτ. intro σ'. specialize (pCn σ').
    asimpl in pCn. by simplify_eq.
  - simpl in *. rewrite (@ids_lt_Closed_n STLCmu.types.type _ _ _ _ _ X n).
    by apply (@ids_lt_Closed_n type _ _ _ _ _ X n).
Qed.

