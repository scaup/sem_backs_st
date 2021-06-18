From iris.program_logic Require Import weakestpre lifting ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.

Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

From st.prelude Require Import big_op_three.

From st.lamst Require Import lang types typing pure_steps.

From st.lam Require Import lang wkpre tactics.
From st.backtranslations.st_sem Require Import help expressions ghost heap_emul.base heap_emul.spec.
From st.backtranslations.st_sem.correctness.sem_le_st.logrel Require Import lift definition compat_help.
From st Require Import resources.

Section compat_lemmas_easy.

  Context `{Σ : !gFunctors} `{sem_le_stΣ_inst : !sem_le_stΣ Σ}.

  Lemma compat_Var (Γ : list type) (x : var) (τ : type) :
    Γ !! x = Some τ → open_exprel_typed Γ (Var x) (lang.Var x) τ.
  Proof.
    intros H. iIntros (Δ vs vs') "Hvsvs".
    iDestruct (big_sepL3_length _ _ _ _ with "Hvsvs") as "[%eq %eq']".
    destruct (Var_subst_list_closed_n_length vs x) as [v [eqv ->]]. apply ids_lt_Closed_n. rewrite -eq. by eapply lookup_lt_Some.
    destruct (lamst.lang.Var_subst_list_closed_n_length vs' x) as [v' [eqv' ->]]. apply ids_lt_Closed_n. rewrite -eq' -eq. by eapply lookup_lt_Some.
    rewrite /exprel_typed /=. iApply lift_val.
    iApply ((big_sepL3_lookup _ _ _ _ x _ _ _ H eqv eqv') with "Hvsvs").
  Qed.

  Lemma compat_Unit (Γ : list type) :
    open_exprel_typed Γ (Lit LitUnit) (lang.Lit lang.LitUnit) TUnit.
  Proof.
    iIntros (Δ vs vs') "Hvsvs". asimpl.
    change (Lit LitUnit) with (of_val $ LitV LitUnit).
    change (lang.Lit lang.LitUnit) with (lang.of_val $ lang.LitV lang.LitUnit).
    iApply lift_val.
    by rewrite valrel_typed_TUnit_unfold.
  Qed.

  Lemma compat_Bool (Γ : list type) (b : bool) :
    open_exprel_typed Γ b b TBool.
  Proof.
    iIntros (Δ vs vs') "Hvsvs". asimpl.
    change (Lit b) with (of_val b).
    change (lang.Lit b) with (lang.of_val b).
    iApply lift_val.
    rewrite valrel_typed_TBool_unfold. by iExists _.
  Qed.

  Lemma compat_Int (Γ : list type) (z : Z) :
    open_exprel_typed Γ z z TInt.
  Proof.
    iIntros (Δ vs vs') "Hvsvs". asimpl.
    change (Lit z) with (of_val z).
    change (lang.Lit z) with (lang.of_val z).
    iApply lift_val.
    rewrite valrel_typed_TInt_unfold. by iExists _.
  Qed.

  Lemma compat_BinOp (Γ : list type) (op : bin_op) e1 e1' e2 e2' :
      open_exprel_typed Γ e1 e1' TInt → open_exprel_typed Γ e2 e2' TInt →
      open_exprel_typed Γ (BinOp op e1 e2) (lang.BinOp op e1' e2') (binop_res_type op).
  Proof.
    intros IHe1 IHe2.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [BinOpLCtx op _] [lang.BinOpLCtx op _]). by iApply IHe1. iIntros (v1 v1') "#Hv1".
    iApply (lift_bind _ [BinOpRCtx op _] [lang.BinOpRCtx op _]). by iApply IHe2. iIntros (v2 v2') "#Hv2".
    rewrite !valrel_typed_TInt_unfold. iDestruct "Hv1" as (z1) "[-> ->]". iDestruct "Hv2" as (z2) "[-> ->]".
    iApply lift_pure_step. apply head_step_pure_step; auto. econstructor; eauto.
    iApply lift_step_later. apply head_prim_step. econstructor; eauto. iNext.
    iApply lift_val.
    destruct op; simpl; (rewrite valrel_typed_TInt_unfold || rewrite valrel_typed_TBool_unfold); by iExists _.
  Qed.

  Lemma compat_Seq (Γ : list type) e1 e1' e2 e2' (τ : type) :
      open_exprel_typed Γ e1 e1' TUnit → open_exprel_typed Γ e2 e2' τ →
      open_exprel_typed Γ (Seq e1 e2) (lang.Seq e1' e2') τ.
  Proof.
    intros IHe1 IHe2.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [SeqCtx _] [lang.SeqCtx _]). by iApply IHe1. iIntros (v1 v1') "#Hv1".
    rewrite !valrel_typed_TUnit_unfold. iDestruct "Hv1" as "[-> ->]".
    iApply lift_pure_step. apply head_step_pure_step; auto. econstructor; eauto.
    iApply lift_step_later. apply head_prim_step. econstructor; eauto. iNext.
    by iApply IHe2.
  Qed.

  Lemma compat_Pair (Γ : list type) e1 e1' e2 e2' (τ1 τ2 : type) :
      open_exprel_typed Γ e1 e1' τ1 → open_exprel_typed Γ e2 e2' τ2 →
      open_exprel_typed Γ (Pair e1 e2) (lang.Pair e1' e2') (τ1 × τ2)%Tₛₜ.
  Proof.
    intros IHe1 IHe2.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [PairLCtx _] [lang.PairLCtx _]). by iApply IHe1. iIntros (v1 v1') "#Hv1".
    iApply (lift_bind _ [PairRCtx _] [lang.PairRCtx _]). by iApply IHe2. iIntros (v2 v2') "#Hv2".
    simpl.
    change (Pair (of_val ?v1) (of_val ?v2)) with (of_val (PairV v1 v2)).
    change (lang.Pair (lang.of_val ?v1) (lang.of_val ?v2))%Eₙₒ with (lang.of_val (lang.PairV v1 v2)).
    iApply lift_val.
    rewrite valrel_typed_TProd_unfold. repeat iExists _; eauto.
  Qed.

  Lemma compat_Fst (Γ : list type) e e' (τ1 τ2 : type) :
      open_exprel_typed Γ e e' (τ1 × τ2)%Tₛₜ → open_exprel_typed Γ (Fst e) (lang.Fst e') τ1.
  Proof.
    intros IHe.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [FstCtx] [lang.FstCtx]). by iApply IHe. iIntros (v v') "#Hv".
    rewrite !valrel_typed_TProd_unfold. iDestruct "Hv" as (v1 v2 v1' v2') "(-> & -> & H1 & H2)".
    iApply lift_pure_step. apply head_step_pure_step; auto. econstructor; by rewrite lang.to_of_val.
    iApply lift_step_later. apply head_prim_step. econstructor; eauto; by rewrite to_of_val.
    by iApply lift_val.
  Qed.

  Lemma compat_Snd (Γ : list type) e e' (τ1 τ2 : type) :
      open_exprel_typed Γ e e' (τ1 × τ2)%Tₛₜ → open_exprel_typed Γ (Snd e) (lang.Snd e') τ2.
  Proof.
    intros IHe.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [SndCtx] [lang.SndCtx]). by iApply IHe. iIntros (v v') "#Hv".
    rewrite !valrel_typed_TProd_unfold. iDestruct "Hv" as (v1 v2 v1' v2') "(-> & -> & H1 & H2)".
    iApply lift_pure_step. apply head_step_pure_step; auto. econstructor; by rewrite lang.to_of_val.
    iApply lift_step_later. apply head_prim_step. econstructor; eauto; by rewrite to_of_val.
    by iApply lift_val.
  Qed.

  Lemma compat_InjL (Γ : list type) e e' (τ1 τ2 : type) :
    open_exprel_typed Γ e e' τ1 → open_exprel_typed Γ (InjL e) (lang.InjL e') (τ1 + τ2)%Tₛₜ.
  Proof.
    intros IHe.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [InjLCtx] [lang.InjLCtx]). by iApply IHe. iIntros (v1 v1') "#Hv1".
    simpl.
    change (InjL (of_val ?v))%Eₙₒ with (of_val (InjLV v)).
    change (lang.InjL (lang.of_val ?v))%Eₙₒ with (lang.of_val (lang.InjLV v)).
    iApply lift_val.
    rewrite valrel_typed_TSum_unfold. repeat iExists _; eauto.
  Qed.

  Lemma compat_InjR (Γ : list type) e e' (τ1 τ2 : type) :
    open_exprel_typed Γ e e' τ2 → open_exprel_typed Γ (InjR e) (lang.InjR e') (τ1 + τ2)%Tₛₜ.
  Proof.
    intros IHe.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [InjRCtx] [lang.InjRCtx]). by iApply IHe. iIntros (v2 v2') "#Hv2". simpl.
    change (InjR (of_val ?v))%Eₙₒ with (of_val (InjRV v)).
    change (lang.InjR (lang.of_val ?v))%Eₙₒ with (lang.of_val (lang.InjRV v)).
    iApply lift_val.
    rewrite valrel_typed_TSum_unfold. repeat iExists _; eauto.
  Qed.

  Lemma compat_Case (Γ : list type) e0 e0' e1 e1' e2 e2' (τ1 τ2 τ3 : type) :
      open_exprel_typed Γ e0 e0' (τ1 + τ2)%Tₛₜ
      → open_exprel_typed (τ1 :: Γ) e1 e1' τ3
      → open_exprel_typed (τ2 :: Γ) e2 e2' τ3 → open_exprel_typed Γ (Case e0 e1 e2) (lang.Case e0' e1' e2') τ3.
  Proof.
    intros IHe0 IHe1 IHe2.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [CaseCtx _ _] [lang.CaseCtx _ _]). by iApply IHe0. iIntros (v v') "#Hv".
    rewrite !valrel_typed_TSum_unfold. iDestruct "Hv" as (vi vi') "[(-> & -> & H) | (-> & -> & H)]".
    - iApply lift_pure_step. apply head_step_pure_step; auto. econstructor; by rewrite lang.to_of_val.
      iApply lift_step_later. apply head_prim_step. econstructor; eauto; by rewrite to_of_val. fold (of_val). fold (lang.of_val). asimpl.
      fold (of_val vi).
      rewrite !subst_list_val_cons lang.subst_list_val_cons. iApply IHe1. simpl. auto.
    - iApply lift_pure_step. apply head_step_pure_step; auto. econstructor; by rewrite lang.to_of_val.
      iApply lift_step_later. apply head_prim_step. econstructor; eauto; by rewrite to_of_val. fold (of_val). fold (lang.of_val). asimpl.
      fold (of_val vi).
      rewrite !subst_list_val_cons lang.subst_list_val_cons. iApply IHe2. simpl. auto.
  Qed.

  Lemma compat_If (Γ : list type) e0 e0' e1 e1' e2 e2' (τ : type) :
    open_exprel_typed Γ e0 e0' TBool → open_exprel_typed Γ e1 e1' τ → open_exprel_typed Γ e2 e2' τ →
    open_exprel_typed Γ (If e0 e1 e2) (lang.If e0' e1' e2') τ.
  Proof.
    intros IHe0 IHe1 IHe2.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [IfCtx _ _] [lang.IfCtx _ _]). by iApply IHe0. iIntros (v v') "#Hv".
    rewrite !valrel_typed_TBool_unfold. iDestruct "Hv" as (b) "[-> ->]".
    destruct b.
    iApply lift_pure_step; first by apply head_step_pure_step; auto; econstructor.
    iApply lift_step_later. apply head_prim_step. econstructor; eauto; by rewrite to_of_val. iNext. by iApply IHe1.
    iApply lift_pure_step; first by apply head_step_pure_step; auto; econstructor.
    iApply lift_step_later. apply head_prim_step. econstructor; eauto; by rewrite to_of_val. iNext. by iApply IHe2.
  Qed.

  Lemma compat_LetIn (Γ : list type) e1 e1' e2 e2' (τ1 τ2 : type) :
      open_exprel_typed Γ e1 e1' τ1 → open_exprel_typed(τ1 :: Γ) e2 e2' τ2 →
      open_exprel_typed Γ (LetIn e1 e2) (lang.LetIn e1' e2') τ2.
  Proof.
    intros IHe1 IHe2.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [LetInCtx _] [lang.LetInCtx _]). by iApply IHe1. iIntros (v1 v1') "#Hv1".
    iApply lift_pure_step. apply head_step_pure_step; auto; econstructor; by rewrite lang.to_of_val.
    iApply lift_step_later. apply head_prim_step. econstructor; eauto; by rewrite to_of_val. iNext. asimpl.
    rewrite subst_list_val_cons lang.subst_list_val_cons. iApply IHe2. simpl. auto.
  Qed.

  Lemma compat_Lam (Γ : list type) e e' (τ1 τ2 : type) :
    open_exprel_typed (τ1 :: Γ) e e' τ2 →
    open_exprel_typed Γ (Lam e) (lang.Lam e') (τ1 ⟶ τ2)%Tₛₜ.
  Proof.
    intros IHe.
    iIntros (Δ vs vs') "#Hvsvs". simpl.
    change (Lam ?e) with (of_val (LamV e)).
    change (lang.Lam ?e) with (lang.of_val (lang.LamV e)).
    iApply lift_val.
    rewrite valrel_typed_TArrow_unfold. iModIntro. iIntros (w w') "Hww".
    iApply lift_pure_step. apply head_step_pure_step; auto; econstructor; by rewrite lang.to_of_val.
    iApply lift_step_later. apply head_prim_step. econstructor; eauto; by rewrite to_of_val. iNext. asimpl.
    rewrite subst_list_val_cons lang.subst_list_val_cons. iApply IHe. simpl. auto.
  Qed.

  Lemma compat_App (Γ : list type) e1 e1' e2 e2' (τ1 τ2 : type) :
      open_exprel_typed Γ e1 e1' (τ1 ⟶ τ2)%Tₛₜ → open_exprel_typed Γ e2 e2' τ1 →
      open_exprel_typed Γ (e1 e2) (e1' e2') τ2.
  Proof.
    intros IHe1 IHe2.
    iIntros (Δ vs vs') "#Hvsvs".
    iApply (lift_bind _ [AppLCtx _] [lang.AppLCtx _]). by iApply IHe1. iIntros (v1 v1') "#Hv1".
    iApply (lift_bind _ [AppRCtx _] [lang.AppRCtx _]). by iApply IHe2. iIntros (v2 v2') "#Hv2".
    rewrite /= valrel_typed_TArrow_unfold. by iApply "Hv1".
  Qed.

  Lemma compat_Fold (Γ : list type) e e' (τ : {bind type}) :
      open_exprel_typed Γ e e' τ.[TRec τ/] → open_exprel_typed Γ (Fold e) (lang.Fold e') (TRec τ).
  Proof.
    intros IHe.
    iIntros (Δ vs vs') "#Hvsvs". simpl.
    iApply (lift_bind _ [FoldCtx] [lang.FoldCtx]). by iApply IHe. iLöb as "IHlob". iIntros (v v') "#Hv".
    simpl. change (Fold (of_val ?v)) with (of_val (FoldV v)).
    change (lang.Fold (lang.of_val ?v)) with (lang.of_val (lang.FoldV v)).
    iApply lift_val.
    rewrite valrel_typed_TRec_unfold. repeat iExists _; eauto.
  Qed.

  Lemma compat_Unfold (Γ : list type) e e' (τ : {bind type}) :
    open_exprel_typed Γ e e' (TRec τ) → open_exprel_typed Γ (Unfold e) (lang.Unfold e') τ.[TRec τ/].
  Proof.
    intros IHe.
    iIntros (Δ vs vs') "#Hvsvs". simpl.
    iApply (lift_bind _ [UnfoldCtx] [lang.UnfoldCtx]). by iApply IHe. iIntros (v v') "#Hv".
    rewrite valrel_typed_TRec_unfold. iDestruct "Hv" as (w w') "(-> & -> & Hw)".
    iApply lift_pure_step. apply head_step_pure_step; auto; econstructor; by rewrite lang.to_of_val.
    iApply lift_step_later. apply head_prim_step. econstructor; eauto; by rewrite to_of_val. iNext. asimpl.
    by iApply lift_val.
  Qed.

End compat_lemmas_easy.

