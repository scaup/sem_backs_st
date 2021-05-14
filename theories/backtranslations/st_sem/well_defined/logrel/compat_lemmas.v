From iris Require Import program_logic.weakestpre.
From iris Require Import base_logic.lib.invariants.
From st.lamst Require Import lang types typing.
From st.lam Require Import lang wkpre generic.lift tactics.
From st.backtranslations.st_sem.well_defined.logrel Require Import definition.
From iris.proofmode Require Import tactics.
From st.backtranslations.st_sem Require Import ghost heap expressions.
From iris_string_ident Require Import ltac2_string_ident.

Section compat_lemmas.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.
  Context `{ghost_mapG_inst : !ghost_mapG Σ nat (prod val val)}.

  Opaque alloc.

  Lemma compat_alloc Γ e e' ρ τ (Hee' : open_exprel_typed Γ e e' τ) :
    open_exprel_typed Γ (alloc e) (alloc e') (TST ρ (TSTref ρ τ)).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    rewrite /= !alloc_Closed.
    iApply (lift_bind' _ _ _ [AppRCtx _] [AppRCtx _] with "Hee'").
    simpl. iIntros (v v') "#Hvv'". iClear "Hee'".
    (* steps *)
    iApply lift_step_later. apply alloc_step.
    iApply lift_step. apply alloc_step.
    iNext.
    (* *)
    iApply lift_val.
    rewrite valrel_typed_TST_unfold.
    destruct ρ; auto. destruct (Δ !! X) as [γ|]eqn:eq; auto.
    (*  *)
    iIntros (psᵢ). iModIntro. iIntros "Hγvs".
    iApply wp_rtc_steps. apply alloc_v_steps.
    change ((encode (psᵢ.*1 ++ [v]), length psᵢ.*1)%Eₙₒ) with (of_val (encode (psᵢ.*1 ++ [v]), length psᵢ.*1)%Vₙₒ). iApply wp_value_fupd'.
    iExists (length psᵢ.*1), (length psᵢ.*2), (psᵢ ++ [(v, v')]).
    iDestruct ((ghost_alloc _ _ (v, v')) with "Hγvs") as "H".
    iApply fupd_trans.
    iMod "H". iModIntro.
    iDestruct "H" as "[H1 H2]". iFrame "H1".
    iSplitR. by rewrite fmap_app /=.
    iSplitR. iModIntro. iPureIntro. rewrite fmap_app /=. apply alloc_v_steps.
    rewrite valrel_typed_TSTRef_unfold. rewrite eq.
    iExists (length psᵢ).
    iSplitR. iPureIntro. by rewrite map_length.
    iSplitR. iPureIntro. by rewrite map_length.
    iApply inv_alloc. iNext. iExists v, v'. auto.
  Qed.

  Opaque read.

  Lemma compat_read Γ e e' ρ τ :
    open_exprel_typed Γ e e' (TSTref ρ τ) →
    open_exprel_typed Γ (read e) (read e') (TST ρ τ).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Hee' Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    rewrite /= !read_Closed.
    iApply (lift_bind' _ _ _ [AppRCtx _] [AppRCtx _] with "Hee'").
    simpl. iIntros (v v') "#Hvv'". iClear "Hee'".
    rewrite valrel_typed_TSTRef_unfold. destruct ρ; auto. destruct (Δ !! X) as [γ|] eqn:eq; auto.
    iDestruct "Hvv'" as (i) "(-> & -> & #HInv)".
    (* steps *)
    iApply lift_step_later. apply read_step.
    iApply lift_step. apply read_step.
    iApply lift_val.
    (* proving relatedness... *)
    rewrite valrel_typed_TST_unfold. rewrite eq.
    iIntros (psᵢ).
    do 2 iModIntro. iIntros "Hγ".
    iInv "HInv" as "HContents" "HClose".

  Admitted.

  Lemma compat_write Γ e1 e1' e2 e2' ρ τ :
    open_exprel_typed Γ e1 e1' (TSTref ρ τ) →
    open_exprel_typed Γ e2 e2' τ →
    open_exprel_typed Γ (write e1 e2) (write e1' e2') (TST ρ TUnit).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Δ vs vs') "#Hvsvs'".
    specialize (IHd1 Δ vs vs').
    iDestruct (IHd1 with "Hvsvs'") as "Hee'". clear IHd1.
    specialize (IHd2 Δ vs vs'). clear IHd2.
    iClear "Hvsvs'".
  Admitted.

  Lemma compat_bind Γ e1 e1' e2 e2' ρ τ1 τ2 :
    open_exprel_typed Γ e1 e1' (TSTref ρ τ1) →
    open_exprel_typed Γ e2 e2' (τ1 ⟶ TST ρ τ2)%Tₛₜ →
    open_exprel_typed Γ (bind e1 e2) (bind e1' e2') (TST ρ τ2).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Δ vs vs') "#Hvsvs'".
    specialize (IHd1 Δ vs vs').
    iDestruct (IHd1 with "Hvsvs'") as "Hee'". clear IHd1.
    specialize (IHd2 Δ vs vs'). clear IHd2.
    iClear "Hvsvs'".
  Admitted.

  Lemma compat_retrn Γ e e' ρ τ :
    open_exprel_typed Γ e e' τ →
    open_exprel_typed Γ (retrn e) (retrn e') (TST ρ τ).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Δ vs vs') "#Hvsvs'".
    specialize (IHd1 Δ vs vs').
    iDestruct (IHd1 with "Hvsvs'") as "Hee'". clear IHd1.
    specialize (IHd2 Δ vs vs'). clear IHd2.
    iClear "Hvsvs'".
  Admitted.

  Lemma compat_runst Γ e e' ρ τ :
    open_exprel_typed (subst (ren (+1)) <$> Γ) e e' (TST (Var 0) τ.[ren (+1)]) →
    open_exprel_typed Γ (runst e) (runst e') τ.
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Δ vs vs') "#Hvsvs'".
    specialize (IHd1 Δ vs vs').
    iDestruct (IHd1 with "Hvsvs'") as "Hee'". clear IHd1.
    specialize (IHd2 Δ vs vs'). clear IHd2.
    iClear "Hvsvs'".
  Admitted.

  Lemma compat_equal Γ e1 e1' e2 e2' ρ τ :
    open_exprel_typed Γ e1 e1' (TSTref ρ τ) →
    open_exprel_typed Γ e2 e2' (TSTref ρ τ) →
    open_exprel_typed Γ (e1 = e2) (e1' = e2') TBool.
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Δ vs vs') "#Hvsvs'".
    specialize (IHd1 Δ vs vs').
    iDestruct (IHd1 with "Hvsvs'") as "Hee'". clear IHd1.
    specialize (IHd2 Δ vs vs'). clear IHd2.
    iClear "Hvsvs'".
  Admitted.

