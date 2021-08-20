From st.prelude Require Import generic forall_three.
From st.STLCmuVS Require Import lang typing types tactics contexts contexts_subst scopedness.

Definition GammaType (Γ : list type) (τ : type) : type := foldr (TArrow) τ (rev Γ).

Lemma GammaType_snoc Γ τ τr : TArrow τ (GammaType Γ τr) = GammaType (Γ ++ [τ]) τr.
Proof. by rewrite /GammaType rev_unit /=. Qed.

Definition LamGamma_ctx (n : nat) : ctx := replicate n CTX_Lam.

Fixpoint LamGamma (n : nat) (e : expr) : expr :=
  match n with
  | O => e
  | S x => Lam (LamGamma x e)
  end.

Lemma fill_LamGamma_ctx (n : nat) (e : expr) : fill_ctx (LamGamma_ctx n) e = LamGamma n e.
Proof. induction n. done. simpl. by rewrite IHn. Qed.

Definition LamGammaV_S (n : nat) (e : expr) : val := LamV (LamGamma n e).

Lemma LamGammaV_S_rw (n : nat) (e : expr) : of_val (LamGammaV_S n e) = LamGamma (S n) e.
Proof. by simpl. Qed.

Lemma LamGamma_ctx_typed (Γ : list type) (τ : type) :
  |C> [] ⊢ₙₒ LamGamma_ctx (length Γ) ☾ Γ; τ ☽ : GammaType Γ τ.
Proof.
  induction Γ as [|τ' τs IHτs] using rev_ind.
  - simpl. by apply TPCTX_nil.
  - rewrite /LamGamma app_length /= Nat.add_1_r.
    rewrite /=. econstructor.
    + rewrite /GammaType rev_unit. simpl. econstructor.
    + fold (GammaType τs). change [τ'] with ([] ++ [τ']).
      by apply typed_ctx_append.
Qed.

Lemma LamGamma_typed e (Γ : list type) (τ : type) (de : typed Γ e τ) :
  [] ⊢ₙₒ LamGamma (length Γ) e : GammaType Γ τ.
Proof.
  rewrite -fill_LamGamma_ctx. eapply typed_ctx_typed. apply de.
  apply LamGamma_ctx_typed.
Qed.

Lemma LamGamma_scoped e n (de : expr_scoped n e) :
  expr_scoped 0 (LamGamma n e).
Proof.
  rewrite -fill_LamGamma_ctx. eapply scoped_ctx_fill. apply de.
  replace n with (length (replicate n TUnit)).
  replace 0 with (length ([] : list type)).
  apply (ctx_typed_scoped _ TUnit _ (GammaType (replicate n TUnit) TUnit)).
  apply LamGamma_ctx_typed. auto. by rewrite replicate_length.
Qed.

Fixpoint AppGamma (F : expr) (es : list expr) : expr :=
  match es with
  | nil => F
  | cons e es' => ((AppGamma F es') e)%Eₙₒ
  end.

Definition AppGamma_ectx (es : list expr) : list ectx_item :=
  fmap AppLCtx (rev es).

Lemma AppGamma_snoc (F : expr) (es : list expr) (e : expr) :
  AppGamma F (es ++ [e]) = AppGamma (F e) es.
Proof.
  induction es.
  - by simpl.
  - simpl. f_equiv. by rewrite IHes.
Qed.

Lemma fill_AppGamma_ectx (F : expr) (es : list expr) : AppGamma F es = fill (AppGamma_ectx es) F.
Proof.
  revert F.
  induction es using rev_ind.
  - done.
  - intro F. by rewrite AppGamma_snoc /AppGamma_ectx rev_unit /= (IHes (F x)).
Qed.

Lemma AppGamma_subst (F : expr) (es : list expr) (σ : var → expr) :
  (AppGamma F es).[σ] = AppGamma F.[σ] (fmap (subst σ) es).
Proof. induction es. by asimpl. asimpl. by rewrite IHes. Qed.

Fixpoint wrap_funs_vars (F : expr) (k : nat) (fs : list val) : expr :=
  match fs with
  | nil => F
  | cons f' fs' => ((wrap_funs_vars F (S k) fs') (f' (Var $ k)))%Eₙₒ
  end.

Lemma wrap_funs_vars_rw (F : expr) (k : nat) (fs : list val) :
  wrap_funs_vars F k fs = AppGamma F (imap (fun l f => (App (of_val f) (Var (l + k)))) fs).
Proof.
  revert k. induction fs as [|f fs IHfs]. done.
  intro k. rewrite /= IHfs (imap_ext _ ((λ (l : nat) (f0 : val), f0 (%(l + k))%Eₙₒ) ∘ S)). done.
  intros. simpl. f_equiv. f_equiv. lia.
Qed.

Lemma wrap_funs_vars_subst1 (F : expr) (k : nat) (fs : list val) (Hfs : Forall (fun f => Closed (of_val f)) fs) σ :
  (wrap_funs_vars F k fs).[upn (length fs + k) σ] = wrap_funs_vars F.[upn (length fs + k) σ] k fs.
Proof.
  rewrite !wrap_funs_vars_rw AppGamma_subst fmap_imap. f_equiv.
  apply imap_ext. intros i f lkp. asimpl. rewrite (upn_lt (i + k) (length fs + k)).
  by rewrite (Forall_lookup_1 _ _ _ _ Hfs lkp).
  assert (i < length fs) by by eapply lookup_lt_Some. lia.
Qed.

Lemma wrap_funs_vars_subst1' l (F : expr) (fs : list val) (Hfs : Forall (fun f => Closed (of_val f)) fs) σ :
  length fs = l → (wrap_funs_vars F 0 fs).[upn l σ] = wrap_funs_vars F.[upn l σ] 0 fs.
Proof. intros <-. replace (length fs) with (length fs + 0) by lia. by apply wrap_funs_vars_subst1. Qed.

(* Fixpoint wrap_funs_vals' (F : expr) (fs vs : list val) (H : length fs = length vs) : expr := *)
(*   match (fs , vs) with *)
(*   | nil, nil => F *)
(*   | cons f fvs => ((wrap_funs_vals F fvs) (f v))%Eₙₒ *)
(*   end. *)

Fixpoint wrap_funs_vals (F : expr) (fvs : list (val * val)) : expr :=
  match fvs with
  | nil => F
  | cons (f, v) fvs => ((wrap_funs_vals F fvs) (f v))%Eₙₒ
  end.

Lemma wrap_funs_vals_rw (F : expr) (fvs : list (val * val)) :
  wrap_funs_vals F fvs = AppGamma F (fmap (fun fv => (App (of_val fv.1) (of_val fv.2))) fvs).
Proof.
  induction fvs as [|[f v] fvs IHfs]. done.
  by rewrite /= IHfs.
Qed.

Lemma wrap_funs_vals_snoc (F : expr) (fvs : list (val * val)) (f v : val) :
  wrap_funs_vals F (fvs ++ [(f, v)]) = wrap_funs_vals (F (f v)) fvs.
Proof. by rewrite !wrap_funs_vals_rw fmap_app AppGamma_snoc. Qed.

Lemma wrap_funs_vars_subst2 (F : expr) (HF : Closed F) (fvs : list (val * val)) (H : Forall (fun f => Closed (of_val f)) fvs.*1) :
  (wrap_funs_vars F 0 fvs.*1).[subst_list_val fvs.*2] = wrap_funs_vals F fvs.
Proof.
  rewrite !wrap_funs_vars_rw wrap_funs_vals_rw AppGamma_subst fmap_imap HF. f_equiv.
  rewrite imap_fmap. rewrite -(imap_const (λ fv : val * val, fv.1 fv.2) fvs).
  apply imap_ext. intros i (f, v) lkp. simpl.
  assert (lkp1 : fvs.*1 !! i = Some f) by by rewrite list_lookup_fmap lkp.
  assert (lkp2 : fvs.*2 !! i = Some v) by by rewrite list_lookup_fmap lkp.
  rewrite (Forall_lookup_1 _ _ _ _ H lkp1) Nat.add_0_r.
  replace (subst_list_val fvs.*2 i) with (ids i).[subst_list_val fvs.*2] by by asimpl. by rewrite (Var_subst_list_val_lookup _ _ _ lkp2).
Qed.

Lemma wrap_funs_vars_subst2' (F : expr) (HF : Closed F) (fs vs : list val) (Hl : length fs = length vs) (H : Forall (fun f => Closed (of_val f)) fs) :
  (wrap_funs_vars F 0 fs).[subst_list_val vs] = wrap_funs_vals F (zip fs vs).
Proof.
  rewrite <- (snd_zip fs vs) at 1 by lia. rewrite <- (fst_zip fs vs) at 2 by lia.
  apply wrap_funs_vars_subst2; auto. rewrite fst_zip; auto; lia.
Qed.

Lemma wrap_funs_vars_typed_help (fs : list val) τr Γ Γ' (H : Forall3 (fun τ' f τ => ∀Γ, Γ ⊢ₙₒ (of_val f) : TArrow τ' τ) Γ' fs Γ) :
  ∀ k, k ≤ length fs → Γ' ++ [GammaType Γ τr] ⊢ₙₒ wrap_funs_vars (Var (length Γ')) (length fs - k) (drop (length fs - k) fs) : GammaType (take (length Γ - k) Γ) τr.
Proof.
  induction k.
  - rewrite !Nat.sub_0_r drop_all firstn_all /=.
    constructor. rewrite lookup_app_r; try lia. by rewrite Nat.sub_diag.
  - destruct (drop (length fs - S k) fs) as [|f rem] eqn:eq.
    + (* exfalso *) destruct fs as [|f' fs'].
      * simpl. intro abs. exfalso. lia.
      * intro plt. exfalso.
        assert (abs : (rev (drop (length (rev (f' :: fs')) - S k) (rev (f' :: fs')))) = []).
        { apply nil_length_inv. rewrite rev_length. rewrite drop_length.
          assert (length (drop (length (f' :: fs') - S k) (f' :: fs')) = 0) by by rewrite eq /=.
          rewrite drop_length in H0. by rewrite rev_length. }
        rewrite -firstn_rev rev_involutive /= in abs. inversion abs.
    + intro plt. specialize (IHk ltac:(lia)). assert (lkp : fs !! (length fs - S k) = Some f).
      { rewrite <- (take_drop (length fs - S k) fs) at 2. rewrite lookup_app_r.
        rewrite take_length_le; try lia. rewrite eq. by replace (length fs - S k - (length fs - S k)) with 0 by lia.
        rewrite take_length_le; lia. }
      simpl. replace (S (length fs - S k)) with (length fs - k) by lia.
      destruct (Forall3_lookup_m _ _ _ _ _ _ H lkp) as (τ' & τ & eq1 & eq2 & P).
      apply App_typed with (τ1 := τ).
      * assert (rem = (drop (length fs - k) fs)) as ->.
        { replace rem with (drop 1 (f :: rem)) by by rewrite /= drop_0.
          rewrite -eq drop_drop. by replace (length fs - S k + 1) with (length fs - k) by lia. }
        assert (TArrow τ (GammaType (take (length Γ - S k) Γ) τr) = GammaType (take (length Γ - k) Γ) τr) as ->.
        { assert (take (length Γ - k) Γ = take (length Γ - S k) Γ ++ [τ]) as ->.
          rewrite -(Forall3_length_lm _ _ _ _ H) (Forall3_length_lr _ _ _ _ H) in eq2.
          rewrite <- (take_drop_middle _ _ _ eq2) at 2. rewrite firstn_app take_take.
          replace ((length Γ - k) `min` (length Γ - S k)) with (length Γ - S k) by lia.
          replace (length Γ - k - length (take (length Γ - S k) Γ)) with 1. by rewrite /= take_0.
          rewrite take_length_le; try lia.
          rewrite -(Forall3_length_lm _ _ _ _ H) (Forall3_length_lr _ _ _ _ H) in plt. lia.
          by apply GammaType_snoc.
        }
        apply IHk.
      * apply App_typed with (τ1 := τ'). apply P. constructor. by apply lookup_app_l_Some.
Qed.

Lemma wrap_funs_vars_typed fs τr Γ Γ' (H : Forall3 (fun τ' f τ => ∀Γ, Γ ⊢ₙₒ of_val f : TArrow τ' τ) Γ' fs Γ) :
  Γ' ++ [GammaType Γ τr] ⊢ₙₒ wrap_funs_vars (Var (length Γ')) 0 fs : τr.
Proof.
  rewrite <- (drop_0 fs).
  replace 0 with (length fs - length fs) by lia.
  replace τr with (GammaType (take (length Γ - length fs) Γ) τr) at 2.
  apply (wrap_funs_vars_typed_help fs τr Γ Γ' H). lia.
  by rewrite -(Forall3_length_lm _ _ _ _ H) (Forall3_length_lr _ _ _ _ H) -minus_diag_reverse /= take_0.
Qed.

Lemma wrap_funs_vals_eval_ctx (e1 e2 : expr) (fvs : list (val * val)) (H : rtc STLCmuVS_step e1 e2) :
  rtc STLCmuVS_step (wrap_funs_vals e1 fvs) (wrap_funs_vals e2 fvs).
Proof.
  induction fvs as [|[f v] fvs IH]; first done.
  by apply (rtc_STLCmuVS_step_ctx (fill [AppLCtx _])).
Qed.

Lemma wrap_funs_vals_eval (fvs : list (val * val)) (vs' : list val) (H : Forall2 (fun fv v' => rtc STLCmuVS_step (of_val fv.1 (of_val fv.2)) (of_val v')) fvs vs') :
  ∀ e, let STLCmuVSgam : expr := (LamGamma (length fvs) e) in
       rtc STLCmuVS_step (wrap_funs_vals STLCmuVSgam fvs) (e.[subst_list_val vs']).
Proof.
  revert H. revert vs'. induction fvs as [|[f v] fvs IHfvs] using rev_ind.
  - intros vs' H; destruct vs' as [|v' vs' _] using rev_ind.
    + intros e. by asimpl.
    + exfalso.
      assert (abs : length ([] : list val) = length (vs' ++ [v'])).
      by rewrite -(Forall2_length _ _ _ H). rewrite /= app_length /= in abs. lia.
  - intros ws' I. destruct ((iffLR (Forall2_app_inv_l _ _ _ _)) I) as (vs' & v' & H & P & ->). clear I.
    destruct v' as [|v' empty]; first by inversion P.
    assert (empty = []) as ->. { apply nil_length_inv. cut (length (v :: empty) = length [(f,v)]); auto. by rewrite (Forall2_length _ _ _ P). }
    inversion_clear P. clear H1. rename H0 into P. simpl in P.
    (* okay *)
    rewrite !app_length !Nat.add_1_r. intros e.
    rewrite /= wrap_funs_vals_snoc. fold (LamGamma (length fvs)).
    change (Lam ?e) with (of_val $ LamV e).
    apply rtc_transitive with (y := wrap_funs_vals (LamGamma (length fvs) e).[of_val v'/] fvs).
    apply wrap_funs_vals_eval_ctx.
    eapply rtc_transitive. apply (rtc_STLCmuVS_step_ctx (fill [AppRCtx _])). apply P. simpl. apply rtc_once. apply head_prim_step. auto_head_step.
    rewrite -fill_LamGamma_ctx subst_fill_ctx.
    assert (scp : |sC> 0 ⊢ₙₒ (LamGamma_ctx (length fvs)) ☾ length fvs ☽).
    { change 0 with (length ([] : list type)).
      rewrite <- (replicate_length (length fvs) TUnit).
      eapply (ctx_typed_scoped _ TUnit _ _).
      apply (LamGamma_ctx_typed (replicate (length fvs) TUnit) TUnit).
    }
    rewrite (subst_closed_ctx _ _ _ scp) (subst_closed_ctx_cont _ _ _ scp).
    rewrite subst_list_val_snoc.
    replace e.[upn (length vs') (of_val v' .: ids) >> subst_list_val vs'] with e.[upn (length vs') (of_val v' .: ids)].[subst_list_val vs'] by by asimpl.
    rewrite -(Forall2_length _ _ _ H).
    specialize (IHfvs vs' H e.[upn (length fvs) ((of_val v') .: ids)]). simpl in IHfvs. rewrite fill_LamGamma_ctx. apply IHfvs.
Qed.

Lemma wrap_funs_vals_eval' (vs' : list val) e (fs vs : list val) l (Hl : l = (length fs)) (Hfs : Forall (fun f => Closed (of_val f)) fs)
      (H : Forall3 (fun f v v' => rtc STLCmuVS_step (of_val f (of_val v)) (of_val v')) fs vs vs') :
  let STLCmuVSgam : expr := (LamGamma l e) in
       rtc STLCmuVS_step (wrap_funs_vals STLCmuVSgam (zip fs vs)) (e.[subst_list_val vs']).
Proof.
  rewrite Hl.
  assert (length fs = length (zip fs vs)) as ->.
  { rewrite <- (fst_zip fs vs) at 1. by rewrite fmap_length.
    rewrite (Forall3_length_lm _ _ _ _ H). lia.
  }
  apply wrap_funs_vals_eval.
  pose proof (Forall3_Forall2 _ _ _ _ H) as H'.
  apply (Forall2_impl _ _ _ _ H'). by intros (a, b) c.
Qed.

Lemma zip_snoc {A B} (ls : list A) l (ks : list B) k : length ls = length ks → zip (ls ++ [l]) (ks ++ [k]) = zip ls ks ++ [(l,k)].
Proof.
  revert ks.
  induction ls as [|l0 ls].
  - intros ks Hl; destruct ks;[|inversion Hl]. by simpl.
  - intros ks Hl; destruct ks as [|k0 ks];[inversion Hl|]. simpl in *.
    rewrite IHls; auto.
Qed.
