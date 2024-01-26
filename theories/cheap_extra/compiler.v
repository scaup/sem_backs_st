From st Require prelude.generic.
From st.STLCmu Require Import types.
From st.STLCmuVS Require Import lang.
From st.backtranslations.sem_syn Require Import gamma_lib sem_le_syn.guard_assert.

Definition grd := (ga_pair Guard).
Definition art := (ga_pair Assert).

Definition compile (e : expr) (Γ : list type) (τ : type) : expr :=
  let Le (*λx1...xn.e *) : expr :=
    LamGamma (length Γ) e in
  let LegΓ (*λx1...xn.e (guardτ1 x1) ... (guardτn xn) *) : expr :=
    wrap_funs_vars Le 0 (map art Γ) in
  grd τ (LegΓ).


From st.STLCmuVS Require Import contexts scopedness typing.
From st.backtranslations.sem_syn Require Import back_ctx.
From st.backtranslations.sem_syn.sem_le_syn Require Import ga_ctx ga_ctx_le_ep_ctx.
From st.STLCmuVS Require Import logrel.adequacy.
From st.cheap_extra Require Import ep_ctx_le_ga_ctx.

Section rrhp_compiler.

  (* Consider an arbitrary interface first *)

  Context (Γ : list type) (τ : type).
  Context (pΓ : Forall Closed Γ) (pτ : Closed τ).

  (* Consider an arbitrary untyped context that's appropriately _scoped_ *)
  Context (C : ctx).
  Context (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽).

  (* We define a appropriately syntactically well-typed context *)
  Definition Cb : ctx :=
    let luC := (CTX_AppR (Lam ()%Eₙₒ)) :: C (* λ_.() C[⋅] *) in
      back_ctx luC Γ τ.

  (* It is indeed appropriately syntactically well-typed context *)
  Lemma Cb_typed : typed_ctx Cb Γ τ [] TUnit.
  Proof.
    apply back_ctx_typed; auto.
    by repeat econstructor.
  Qed.

  Notation equiterminate e e' :=
    (STLCmuVS_halts e <-> STLCmuVS_halts e').

 Lemma equiterminate_l e e2 e' :
    STLCmuVS_step e e2 →
    (STLCmuVS_halts e2 <-> STLCmuVS_halts e') →
    (STLCmuVS_halts e <-> STLCmuVS_halts e').
  Proof.
    intros; split; intros.
    - destruct H1 as [a H1]. apply H0. eexists. eapply lift.anti_step_help; eauto.
    - destruct H1 as [a H1]. assert (H' : STLCmuVS_halts e2). { apply H0. by exists a. }
      destruct H' as [b H']. exists b. by econstructor.
  Qed.

  Lemma equiterminate_eq e e' :
    e = e' →
    (STLCmuVS_halts e <-> STLCmuVS_halts e').
  Proof. by intros ->. Qed.

  Lemma helper_blabla : ∀ n e K,
    (∃ v, nsteps STLCmuVS_step n (fill K e) (of_val v)) → STLCmuVS_halts e.
  Proof.
    induction n; intros; destruct H as [v H].
    - inversion H.
      destruct (fill_val e K) as [w G]. eexists. by rewrite H0 to_of_val.
      exists w. rewrite (of_to_val _ _ G). apply rtc_refl.
    - inversion_clear H. rename y into e'.
      destruct (to_val e) eqn:eq. exists v0. by rewrite (of_to_val _ _ eq).
      destruct (@fill_step_inv STLCmuVS_lang (fill K) _ _ tt [] e' tt [] eq H0) as [e2 [eq' step]].
      assert (∃ v : val, nsteps STLCmuVS_step n (fill K e2) v). exists v. by rewrite -eq'.
      specialize (IHn e2 K H).
      destruct IHn as [w HHH]. exists w. eapply rtc_l. by apply step. auto.
  Qed.

  (* Cb emulates C with respect to arbitrary e and [[e]]  *)
  Lemma rrhp_compiler (e : expr) (de : Γ ⊢ₙₒ e : τ) :
    equiterminate (fill_ctx Cb e) (fill_ctx C (compile e Γ τ)).
  Proof.
    rewrite /Cb. auto.
    apply (@iff_trans _ (STLCmuVS_halts (fill_ctx (ga_ctx ((CTX_AppR (Lam ()%Eₙₒ)) :: C) Γ τ) e)) _).
    (* main result of logical relatedness... *)
    { split.
      - apply exprel_adequate.
        intros Σ irisGS_inst. simpl.
        apply definitions.open_exprel_typed_nil'.
        apply (rel_ep_ctx_le_ga_ctx); eauto.
          by repeat econstructor.
          by eapply expr_typed_scoped.
          by eapply expr_typed_scoped.
          by apply fundamental.auto_related_typed_expr.
      - apply exprel_adequate.
        intros Σ irisGS_inst. simpl.
        apply definitions.open_exprel_typed_nil'.
        apply (rel_ga_ctx_le_ep_ctx); eauto.
          by repeat econstructor.
          by eapply expr_typed_scoped.
          by eapply expr_typed_scoped.
          by apply fundamental.auto_related_typed_expr. }
    (* take possible one step to fit *)
    apply (@iff_trans _ (STLCmuVS_halts (fill_ctx (CTX_AppR (ga_pair Assert TUnit) :: (CTX_AppR (Lam ()%Eₙₒ)) :: C) (compile e Γ τ))) _).
    { destruct (length Γ) as [|n] eqn:eq; rewrite /= /ga_ctx eq.
      - destruct Γ as [|abs]; try by inversion abs.
        by rewrite /ga_ctx_nil /compile /= /LamGamma -fill_ctx_app /=.
      - eapply equiterminate_l. rewrite /ga_ctx_cons /= eq /=. apply head_prim_step. econstructor; auto.
        apply equiterminate_eq.
        change (Lam (fill_ctx (replicate n CTX_Lam) e)) with
          ((fill_ctx (replicate (S n) CTX_Lam) e)). rewrite -eq.
        simpl. asimpl. do 2 f_equal.
        rewrite contexts_subst.subst_fill_ctx.
        rewrite (contexts_subst.subst_closed_ctx _ _ _ pCscp).
        f_equal. rewrite /= ga_pair_closed; auto. rewrite /compile.
        f_equal.
        rewrite (contexts_subst.subst_closed_ctx_cont _ _ _ pCscp).
        rewrite -eq.
        rewrite wrap_funs_vars_subst1'.
        f_equal.
        replace ((length Γ)) with ((length Γ) + 0) at 3 by by lia.
        rewrite (ids_subst_yes (length Γ) 0). simpl.
        change (replicate (length Γ) CTX_Lam) with (LamGamma_ctx (length Γ)). rewrite fill_LamGamma_ctx. asimpl.
        assert (H : Closed (LamGamma (length Γ) e)). apply expr_Closed_n. apply LamGamma_scoped. by eapply expr_typed_scoped.
        by rewrite H.
        apply Forall_fmap. apply (Forall_impl _ _ _ pΓ). intros. simpl. by apply ga_pair_closed.
        by rewrite fmap_length. }
    (* should be easy *)  simpl.
    { split; intros. destruct H as [v H].
      - destruct (iffLR (rtc_nsteps _ _) H) as [n H'].
        eapply (helper_blabla n _ [AppRCtx (LamV _); AppRCtx (LamV _) ]). eexists. apply H'.
      - destruct H as [v H]. exists ()%Vₙₒ.
        eapply (rtc_transitive _ ((Lam (Seq (%0)%Eₙₒ ()%Eₙₒ)
       (Lam ()%Eₙₒ (v))) )).
        change (Lam ?e) with (of_val $ LamV e).
        change (LamV ?w ((LamV ?b) ?t)) with (fill [AppRCtx (LamV b); AppRCtx (LamV w) ] t).
        eapply (rtc_congruence (fill _) STLCmuVS_step _ _ (fun x y => (@fill_step _ (fill _) _ x tt [] y tt [])) H).
        eapply rtc_l. change (Lam ?e) with (of_val $ LamV e). eapply (Ectx_step ([AppRCtx _ ])); eauto. econstructor; auto. by rewrite to_of_val.
        eapply rtc_l. apply head_prim_step. econstructor; auto.
        eapply rtc_l. apply head_prim_step. econstructor; auto.
        econstructor; auto. }
  Qed.

Section rrhp_compiler.
