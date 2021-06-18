From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.lam Require Import lang types typing wkpre generic.lift contexts logrel.definitions tactics.
From st.prelude Require Import big_op_three.
From st Require Import resources.

Canonical Structure typeO := leibnizO type.

Section definition.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  (* We define a stuckness-sensistive and insensitive one *)
  Context (s : stuckness).

  Lemma compat_Var (Γ : list type) (x : var) (τ : type) :
    Γ !! x = Some τ → open_exprel_typed s Γ (%x)%Eₙₒ (%x)%Eₙₒ τ.
  Proof.
    intros H. iIntros (vs vs') "Hvsvs".
    iDestruct (big_sepL3_length _ _ _ _ with "Hvsvs") as "[%eq %eq']".
    destruct (Var_subst_list_closed_n_length vs x) as [v [eqv ->]]. apply ids_lt_Closed_n. rewrite -eq. by eapply lookup_lt_Some.
    destruct (Var_subst_list_closed_n_length vs' x) as [v' [eqv' ->]]. apply ids_lt_Closed_n. rewrite -eq' -eq. by eapply lookup_lt_Some.
    rewrite /exprel_typed /=. iApply lift_val.
    iApply ((big_sepL3_lookup _ _ _ _ x _ _ _ H eqv eqv') with "Hvsvs").
  Qed.

  Lemma lift_bind (Kᵢ Kₛ : list ectx_item) (Φ Ψ : valO -n> valO -n> iPropO Σ) (eᵢ eₛ : expr) :
    ⊢ lift s Φ eᵢ eₛ -∗ (∀ vᵢ vₛ, Φ vᵢ vₛ -∗ lift s Ψ (fill Kᵢ (of_val vᵢ)) (fill Kₛ (of_val vₛ))) -∗ lift s Ψ (fill Kᵢ eᵢ) (fill Kₛ eₛ).
  Proof. iIntros "H H2". iApply lift.lift_bind. iFrame. Qed.

  Lemma compat_Unit (Γ : list type) :
    open_exprel_typed s Γ ()%Eₙₒ ()%Eₙₒ TUnit.
  Proof.
    iIntros (vs vs') "Hvsvs". asimpl.
    change ()%Eₙₒ with (of_val ()%Vₙₒ). iApply lift_val.
    by rewrite valrel_typed_TUnit_unfold.
  Qed.

  Lemma compat_Bool (Γ : list type) (b : bool) :
    open_exprel_typed s Γ b b TBool.
  Proof.
    iIntros (vs vs') "Hvsvs". asimpl.
    change (Lit b)%Eₙₒ with (of_val b). iApply lift_val.
    rewrite valrel_typed_TBool_unfold. by iExists _.
  Qed.

  Lemma compat_Int (Γ : list type) (z : Z) :
    open_exprel_typed s Γ z z TInt.
  Proof.
    iIntros (vs vs') "Hvsvs". asimpl.
    change (Lit z)%Eₙₒ with (of_val z). iApply lift_val.
    rewrite valrel_typed_TInt_unfold. by iExists _.
  Qed.

  Lemma compat_BinOp (Γ : list type) (op : bin_op) (e1 e1' e2 e2' : expr) :
      open_exprel_typed s Γ e1 e1' TInt → open_exprel_typed s Γ e2 e2' TInt →
      open_exprel_typed s Γ (BinOp op e1 e2) (BinOp op e1' e2') (binop_res_type op).
  Proof.
    intros IHe1 IHe2.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [BinOpLCtx op _] [BinOpLCtx op _]). by iApply IHe1. iIntros (v1 v1') "#Hv1".
    iApply (lift_bind [BinOpRCtx op _] [BinOpRCtx op _]). by iApply IHe2. iIntros (v2 v2') "#Hv2".
    rewrite !valrel_typed_TInt_unfold. iDestruct "Hv1" as (z1) "[-> ->]". iDestruct "Hv2" as (z2) "[-> ->]".
    iApply lift_step. auto_lam_step.
    iApply lift_step_later. auto_lam_step. iNext. simpl.
    iApply lift_val.
    destruct op; simpl; (rewrite valrel_typed_TInt_unfold || rewrite valrel_typed_TBool_unfold); by iExists _.
  Qed.

  Lemma compat_Seq (Γ : list type) (e1 e1' e2 e2' : expr) (τ : type) :
      open_exprel_typed s Γ e1 e1' TUnit → open_exprel_typed s Γ e2 e2' τ →
      open_exprel_typed s Γ (Seq e1 e2) (Seq e1' e2') τ.
  Proof.
    intros IHe1 IHe2.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [SeqCtx _] [SeqCtx _]). by iApply IHe1. iIntros (v1 v1') "#Hv1".
    rewrite !valrel_typed_TUnit_unfold. iDestruct "Hv1" as "[-> ->]".
    iApply lift_step. auto_lam_step.
    iApply lift_step_later. auto_lam_step. iNext. simpl.
    by iApply IHe2.
  Qed.

  Lemma compat_Pair (Γ : list type) (e1 e1' e2 e2' : expr) (τ1 τ2 : type) :
      open_exprel_typed s Γ e1 e1' τ1 → open_exprel_typed s Γ e2 e2' τ2 →
      open_exprel_typed s Γ (e1, e2)%Eₙₒ (e1', e2')%Eₙₒ (τ1 × τ2)%Tₙₒ.
  Proof.
    intros IHe1 IHe2.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [PairLCtx _] [PairLCtx _]). by iApply IHe1. iIntros (v1 v1') "#Hv1".
    iApply (lift_bind [PairRCtx _] [PairRCtx _]). by iApply IHe2. iIntros (v2 v2') "#Hv2".
    simpl. change (of_val ?v1, of_val ?v2)%Eₙₒ with (of_val (PairV v1 v2)). iApply lift_val.
    rewrite valrel_typed_TProd_unfold. repeat iExists _; eauto.
  Qed.

  Lemma compat_Fst (Γ : list type) (e e' : expr) (τ1 τ2 : type) :
      open_exprel_typed s Γ e e' (τ1 × τ2)%Tₙₒ → open_exprel_typed s Γ (Fst e) (Fst e') τ1.
  Proof.
    intros IHe.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [FstCtx] [FstCtx]). by iApply IHe. iIntros (v v') "#Hv".
    rewrite !valrel_typed_TProd_unfold. iDestruct "Hv" as (v1 v2 v1' v2') "(-> & -> & H1 & H2)".
    iApply lift_step. auto_lam_step.
    iApply lift_step_later. auto_lam_step. iNext. simplify_custom. by iApply lift_val.
  Qed.

  Lemma compat_Snd (Γ : list type) (e e' : expr) (τ1 τ2 : type) :
      open_exprel_typed s Γ e e' (τ1 × τ2)%Tₙₒ → open_exprel_typed s Γ (Snd e) (Snd e') τ2.
  Proof.
    intros IHe.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [SndCtx] [SndCtx]). by iApply IHe. iIntros (v v') "#Hv".
    rewrite !valrel_typed_TProd_unfold. iDestruct "Hv" as (v1 v2 v1' v2') "(-> & -> & H1 & H2)".
    iApply lift_step. auto_lam_step.
    iApply lift_step_later. auto_lam_step. iNext. simplify_custom. by iApply lift_val.
  Qed.

  Lemma compat_InjL (Γ : list type) (e e' : expr) (τ1 τ2 : type) :
    open_exprel_typed s Γ e e' τ1 → open_exprel_typed s Γ (InjL e) (InjL e') (τ1 + τ2)%Tₙₒ.
  Proof.
    intros IHe.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [InjLCtx] [InjLCtx]). by iApply IHe. iIntros (v1 v1') "#Hv1".
    simpl. change (InjL (of_val ?v))%Eₙₒ with (of_val (InjLV v)). iApply lift_val.
    rewrite valrel_typed_TSum_unfold. repeat iExists _; eauto.
  Qed.

  Lemma compat_InjR (Γ : list type) (e e' : expr) (τ1 τ2 : type) :
    open_exprel_typed s Γ e e' τ2 → open_exprel_typed s Γ (InjR e) (InjR e') (τ1 + τ2)%Tₙₒ.
  Proof.
    intros IHe.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [InjRCtx] [InjRCtx]). by iApply IHe. iIntros (v2 v2') "#Hv2".
    simpl. change (InjR (of_val ?v))%Eₙₒ with (of_val (InjRV v)). iApply lift_val.
    rewrite valrel_typed_TSum_unfold. repeat iExists _; eauto.
  Qed.

  Lemma compat_Case (Γ : list type) (e0 e0' e1 e1' e2 e2' : expr) (τ1 τ2 τ3 : type) :
      open_exprel_typed s Γ e0 e0' (τ1 + τ2)%Tₙₒ
      → open_exprel_typed s (τ1 :: Γ) e1 e1' τ3
      → open_exprel_typed s (τ2 :: Γ) e2 e2' τ3 → open_exprel_typed s Γ (Case e0 e1 e2) (Case e0' e1' e2') τ3.
  Proof.
    intros IHe0 IHe1 IHe2.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [CaseCtx _ _] [CaseCtx _ _]). by iApply IHe0. iIntros (v v') "#Hv".
    rewrite !valrel_typed_TSum_unfold. iDestruct "Hv" as (vi vi') "[(-> & -> & H) | (-> & -> & H)]".
    - iApply lift_step. auto_lam_step. iApply lift_step_later. auto_lam_step. iNext. simplify_custom.
      rewrite !subst_list_val_cons. iApply IHe1. simpl. auto.
    - iApply lift_step. auto_lam_step. iApply lift_step_later. auto_lam_step. iNext. simplify_custom.
      rewrite !subst_list_val_cons. iApply IHe2. simpl. auto.
  Qed.

  Lemma compat_If (Γ : list type) (e0 e0' e1 e1' e2 e2' : expr) (τ : type) :
    open_exprel_typed s Γ e0 e0' TBool → open_exprel_typed s Γ e1 e1' τ → open_exprel_typed s Γ e2 e2' τ →
    open_exprel_typed s Γ (If e0 e1 e2) (If e0' e1' e2') τ.
  Proof.
    intros IHe0 IHe1 IHe2.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [IfCtx _ _] [IfCtx _ _]). by iApply IHe0. iIntros (v v') "#Hv".
    rewrite !valrel_typed_TBool_unfold. iDestruct "Hv" as (b) "[-> ->]".
    destruct b; (iApply lift_step; first by auto_lam_step); (iApply lift_step_later; first by auto_lam_step); iNext; simpl;
      [by iApply IHe1 | by iApply IHe2].
  Qed.

  Lemma compat_LetIn (Γ : list type) (e1 e1' e2 e2' : expr) (τ1 τ2 : type) :
      open_exprel_typed s Γ e1 e1' τ1 → open_exprel_typed s (τ1 :: Γ) e2 e2' τ2 →
      open_exprel_typed s Γ (LetIn e1 e2) (LetIn e1' e2') τ2.
  Proof.
    intros IHe1 IHe2.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [LetInCtx _] [LetInCtx _]). by iApply IHe1. iIntros (v1 v1') "#Hv1".
    iApply lift_step; first by auto_lam_step. iApply lift_step_later; first by auto_lam_step. iNext. simplify_custom.
    rewrite !subst_list_val_cons. iApply IHe2. simpl. auto.
  Qed.

  Lemma compat_Lam (Γ : list type) (e e' : expr) (τ1 τ2 : type) :
    open_exprel_typed s (τ1 :: Γ) e e' τ2 →
    open_exprel_typed s Γ (Lam e) (Lam e') (τ1 ⟶ τ2)%Tₙₒ.
  Proof.
    intros IHe.
    iIntros (vs vs') "#Hvsvs". simpl.
    change (Lam ?e) with (of_val (LamV e)). iApply lift_val.
    rewrite valrel_typed_TArrow_unfold. iModIntro. iIntros (w w') "Hww".
    iApply lift_step; first by auto_lam_step. iApply lift_step_later; first by auto_lam_step. iNext. simplify_custom.
    rewrite !subst_list_val_cons. iApply IHe. simpl. auto.
  Qed.

  Lemma compat_App (Γ : list type) (e1 e1' e2 e2' : expr) (τ1 τ2 : type) :
      open_exprel_typed s Γ e1 e1' (τ1 ⟶ τ2)%Tₙₒ → open_exprel_typed s Γ e2 e2' τ1 →
      open_exprel_typed s Γ (e1 e2) (e1' e2') τ2.
  Proof.
    intros IHe1 IHe2.
    iIntros (vs vs') "#Hvsvs".
    iApply (lift_bind [AppLCtx _] [AppLCtx _]). by iApply IHe1. iIntros (v1 v1') "#Hv1".
    iApply (lift_bind [AppRCtx _] [AppRCtx _]). by iApply IHe2. iIntros (v2 v2') "#Hv2".
    rewrite /= valrel_typed_TArrow_unfold. by iApply "Hv1".
  Qed.

  Lemma compat_Fold (Γ : list type) (e e' : expr) (τ : {bind type}) :
      open_exprel_typed s Γ e e' τ.[TRec τ/] → open_exprel_typed s Γ (Fold e) (Fold e') (TRec τ).
  Proof.
    intros IHe.
    iIntros (vs vs') "#Hvsvs". simpl.
    iApply (lift_bind [FoldCtx] [FoldCtx]). by iApply IHe. iLöb as "IHlob". iIntros (v v') "#Hv".
    simpl. change (Fold (of_val ?v)) with (of_val (FoldV v)). iApply lift_val.
    rewrite valrel_typed_TRec_unfold. repeat iExists _; eauto.
  Qed.

  Lemma compat_Unfold (Γ : list type) (e e' : expr) (τ : {bind type}) :
    open_exprel_typed s Γ e e' (TRec τ) → open_exprel_typed s Γ (Unfold e) (Unfold e') τ.[TRec τ/].
  Proof.
    intros IHe.
    iIntros (vs vs') "#Hvsvs". simpl.
    iApply (lift_bind [UnfoldCtx] [UnfoldCtx]). by iApply IHe. iIntros (v v') "#Hv".
    rewrite valrel_typed_TRec_unfold. iDestruct "Hv" as (w w') "(-> & -> & Hw)".
    iApply lift_step; first by auto_lam_step. iApply lift_step_later; first by auto_lam_step. iNext. simplify_custom.
    by iApply lift_val.
  Qed.

End definition.

Ltac unfold_valrel_typed :=
  (rewrite valrel_typed_TUnit_unfold) ||
  (rewrite valrel_typed_TBool_unfold) ||
  (rewrite valrel_typed_TInt_unfold) ||
  (rewrite valrel_typed_TArrow_unfold) ||
  (rewrite valrel_typed_TSum_unfold) ||
  (rewrite valrel_typed_TProd_unfold) ||
  (rewrite valrel_typed_TRec_unfold).

Ltac simpl_valrel_typed := fold (valrel_typed_gen_pre); repeat rewrite valrel_typed_gen_pre_gen -valrel_typed_unfold; fold (valrel_typed).
