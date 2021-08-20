From iris.program_logic Require Import weakestpre lifting ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.

Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

From st.prelude Require Import big_op_three.

From st.STLCmuVS Require Import lang.
From st.STLCmuST Require Import wkpre lang types typing.

From st.backtranslations.st_sem Require Import expressions ghost heap_emul.base heap_emul.spec.
From st.backtranslations.st_sem.correctness.st_le_sem.logrel Require Import lift definition compat_help.
From st Require Import resources.

Section compat_lemmas.

  Context `{Σ : !gFunctors} `{st_le_semΣ_inst : !st_le_semΣ Σ}.

  Opaque alloc alloc_v encode.

  Lemma compat_alloc Γ e e' ρ τ (Hee' : open_exprel_typed Γ e e' τ) :
    open_exprel_typed Γ (Alloc e) (alloc e') (TST ρ (TSTref ρ τ)).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    rewrite /= !alloc_Closed.
    iApply (lift_bind _ [AllocCtx] [STLCmuVS.lang.AppRCtx _] with "Hee'"). iClear "Hee'".
    iIntros (v v') "#Hvv'". simpl.
    (* ok *)
    iApply lift_step. apply alloc_step.
    change (Alloc v) with (of_val (AllocV v)). iApply lift_val.
    rewrite valrel_typed_TST_unfold. destruct ρ; auto. destruct (Δ !! X) as [[γ γ']|]eqn:eq; auto.
    (*  *)
    iIntros (psᵢ). iModIntro. iIntros "[AuthLocs AuthVals]".
    iApply wp_fupd. iApply wp_wand. iApply wp_alloc.
    iIntros (x) "Hdes". iDestruct "Hdes" as (l) "[-> Hlv]".
    iDestruct ((ghost_alloc_persist γ psᵢ.*1 l) with "AuthLocs") as ">[AuthLocsFin Hloc]".
    iMod ((ghost_alloc γ' psᵢ.*2 v') with "AuthVals") as "[AuthValsFin Hval]".
    iExists (length psᵢ.*2), (psᵢ ++ [(l, v')]). rewrite !fmap_app /=. iFrame "AuthLocsFin AuthValsFin".
    iSplitL "". iPureIntro. apply alloc_v_steps.
    rewrite valrel_typed_TSTRef_unfold. rewrite eq.
    iExists (length psᵢ.*1), l. iFrame "Hloc". iSplitL ""; auto. iSplitL ""; rewrite !fmap_length; auto.
    iApply inv_alloc. iExists v, v'. iNext. by iFrame.
  Qed.

  Opaque read read_i.

  Lemma compat_read Γ e e' ρ τ :
    open_exprel_typed Γ e e' (TSTref ρ τ) →
    open_exprel_typed Γ (Read e) (read e') (TST ρ τ).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Hee' Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    rewrite /= !read_Closed.
    iApply (lift_bind _ [ReadCtx] [STLCmuVS.lang.AppRCtx _] with "Hee'").
    simpl. iIntros (v v') "#Hvv'". iClear "Hee'".
    rewrite valrel_typed_TSTRef_unfold. destruct ρ; auto. destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
    iDestruct "Hvv'" as (i l) "(-> & Hloc & -> & #HInv)".
    (* steps *)
    change (Lit l) with (of_val l). change (Read (of_val l)) with (of_val (ReadV l)).
    iApply lift_step. apply read_step.
    iApply lift_val.
    rewrite valrel_typed_TST_unfold. rewrite eq.
    iIntros (psᵢ). iModIntro. iIntros "[AuthLocs AuthVals]".
    iApply wp_lift_step; auto. simpl. iIntros (σ1 n κ κ' m) "Hglob".
    (* rewrite wp_unfold /wp_pre. simpl. *)
    iInv "HInv" as (w w') "(>Hiγ'w' & >Hlw & #Hww)" "HClose".
    iAssert (⌜ σ1 !! l = Some w⌝)%I with "[Hlw Hglob]" as "%H". iApply (gen_heap_valid with "Hglob Hlw").
    iAssert (⌜ psᵢ.*2 !! i = Some w'⌝)%I with "[Hiγ'w' AuthVals]" as "%Hw'". iApply (ghost_read with "AuthVals Hiγ'w'").
    iApply fupd_frame_l. iSplitL "".
    { iPureIntro. auto.
      (* exists [], (RunST $ Return w), σ1, []. *)
      (* apply head_prim_step. econstructor. apply head_prim_step. by econstructor. *)
    }
    iApply (fupd_trans _ ⊤ _).
    iApply fupd_wand_r. iSplitL "HClose Hiγ'w' Hlw". iApply "HClose". iNext. iExists w, w'. by iFrame.
    iIntros (_).
    iApply fupd_mask_intro. set_solver. iIntros "Hclose".
    iNext. iIntros (e2 σ2 efs) "%Hstep".
    iMod "Hclose". iModIntro.
    destruct (inv_prim_step_RunST_Read _ _ _ _ _ _ Hstep) as (v & eq' & -> & -> & -> & ->).
    rewrite H in eq'. inversion eq'. rewrite -!H1.
    iFrame "Hglob". simpl. iSplit; auto.
    iApply wp_pure_step_later. apply pure_step_RunST_Return_val. iNext. iApply wp_value'.
    iExists w', psᵢ. iFrame. iFrame "Hww". iPureIntro. by apply read_i_steps.
  Qed.

  Lemma compat_write Γ e1 e1' e2 e2' ρ τ :
    open_exprel_typed Γ e1 e1' (TSTref ρ τ) →
    open_exprel_typed Γ e2 e2' τ →
    open_exprel_typed Γ (Write e1 e2) (write e1' e2') (TST ρ TUnit).
  Proof.
    Local Opaque write write_i write_i_v.
    (* cleaning and getting to the gist of it *)
    iIntros (H1 H2 Δ vs vs') "#Hvsvs'".
    specialize (H1 Δ vs vs'). specialize (H2 Δ vs vs').
    iDestruct (H1 with "Hvsvs'") as "H1". clear H1. iDestruct (H2 with "Hvsvs'") as "H2". clear H2.
    iClear "Hvsvs'".
    change ((write ?e1 ?e2).[?σ]) with (write e1.[σ] e2.[σ]).
    iApply (lift_bind _ [WriteLCtx _] [STLCmuVS.lang.AppRCtx _; STLCmuVS.lang.AppLCtx _] with "H1"). simpl.
    iIntros (v1 v1') "#Hv1v1'". iClear "H1".
    iApply lift_step. apply (@STLCmuVS_step_ctx (STLCmuVS.lang.fill_item (STLCmuVS.lang.AppLCtx _)) (ectxi_lang_ctx_item _)). apply write_step. simpl.
    iApply (lift_bind _ [WriteRCtx _] [STLCmuVS.lang.AppRCtx _] with "H2"). iClear "H2".
    iIntros (v2 v2') "#Hv2v2'". simpl.
    iApply lift_step. apply write_i_step.
    change (Write v1 v2) with (of_val $ WriteV v1 v2).
    iApply lift_val.
    (* okay *)
    iEval (rewrite valrel_typed_TSTRef_unfold) in "Hv1v1'".
    rewrite valrel_typed_TST_unfold; destruct ρ; auto; destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
    iDestruct "Hv1v1'" as (i l) "(-> & Hil & -> & HInv)".
    iIntros (psᵢ). iModIntro. iIntros "[AuthLocs AuthVals]".
    iApply wp_lift_step; auto. simpl. iIntros (σ1 n κ κ' m) "Hglob".
    iInv "HInv" as (w w') "(>Hiγ'w' & >Hlw & #Hww)" "HClose".
    iDestruct (gen_heap_valid with "Hglob Hlw") as "%Hlw".
    iDestruct (ghost_read with "AuthVals Hiγ'w'") as "%Hiw'".
    iMod (ghost_write γ' psᵢ.*2 w' i v2' with "AuthVals Hiγ'w'") as "[AuthVals Hiγ'v2']".
    iMod (gen_heap_update σ1 l w v2 with "Hglob Hlw") as "[Hglob Hlv2]".
    iApply fupd_frame_l. iSplitL "". iPureIntro.
    { auto.
      (* exists [], (RunST $ Return ()%Vₛₜ), (<[ l := v2 ]> σ1), []. apply head_prim_step. econstructor. *)
      (* apply head_prim_step. econstructor. by eexists. by rewrite to_of_val. *)
    }
    iApply fupd_mask_intro. set_solver. iIntros "Hclosetriv".
    iNext. iIntros (e' σ2 efs) "%Hstep". iMod "Hclosetriv". iClear "Hclosetriv".
    destruct (inv_prim_step_RunST_Write_val _ _ _ _ _ _ _ Hstep) as (HiS & -> & -> & -> & ->).
    iApply fupd_wand_r. iSplitL "HClose Hiγ'v2' Hlv2". iApply "HClose". iExists v2, v2'. by iFrame.
    iIntros (_). iFrame "Hglob". iSplitR ""; auto.
    iApply wp_pure_step_later. apply pure_step_RunST_Return_val. iNext. iApply wp_value'.
    iExists ()%Vₙₒ, (zip psᵢ.*1 (<[i := v2']> psᵢ.*2)).
    rewrite fst_zip; [|by rewrite insert_length !fmap_length].
    rewrite snd_zip; [|by rewrite insert_length !fmap_length].
    rewrite valrel_typed_TUnit_unfold.
    iFrame "AuthLocs AuthVals". iSplit; auto. iPureIntro.
    by eapply write_i_v_steps.
  Qed.

  Opaque bind bind_v bind_v_f.

  Lemma compat_bind Γ e1 e1' e2 e2' ρ τ1 τ2 :
    open_exprel_typed Γ e1 e1' (TST ρ τ1) →
    open_exprel_typed Γ e2 e2' (τ1 ⟶ TST ρ τ2)%Tₛₜ →
    open_exprel_typed Γ (Bind e1 e2) (bind e1' e2') (TST ρ τ2).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (H1 H2 Δ vs vs') "#Hvsvs'".
    specialize (H1 Δ vs vs'). specialize (H2 Δ vs vs').
    iDestruct (H1 with "Hvsvs'") as "H1". clear H1. iDestruct (H2 with "Hvsvs'") as "H2". clear H2.
    iClear "Hvsvs'".
    change ((bind ?e1 ?e2).[?σ]) with (bind e1.[σ] e2.[σ]).
    change ((Bind ?e1 ?e2).[?σ]) with (Bind e1.[σ] e2.[σ]).
    iApply (lift_bind _ [BindLCtx _] [STLCmuVS.lang.AppRCtx _; STLCmuVS.lang.AppLCtx _] with "H1"). simpl.
    iIntros (v1 v1') "#Hv1v1'". iClear "H1".
    iApply lift_step. apply (@STLCmuVS_step_ctx (STLCmuVS.lang.fill_item (STLCmuVS.lang.AppLCtx _)) (ectxi_lang_ctx_item _)). apply bind_step. simpl.
    iApply (lift_bind _ [BindRCtx _] [STLCmuVS.lang.AppRCtx _] with "H2").
    iIntros (v2 v2') "#Hv2v2'". simpl.
    iApply lift_step. apply bind_v_step.
    change (Bind (of_val ?v1) (of_val ?v2)) with (of_val $ BindV v1 v2).
    iApply lift_val.
    (* okay *)
    (* rewrite /bind_v_f. *)
    iEval (rewrite valrel_typed_TST_unfold) in "Hv1v1'".
    iEval (rewrite valrel_typed_TST_unfold). destruct ρ; auto. destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
    iIntros (ps0). iModIntro. iIntros "Auth".
    iSpecialize ("Hv1v1'" $! ps0 with "Auth").
    iApply wp_runst_bind. fold of_val. iApply (wp_wand with "Hv1v1'").
    iIntros (v) "Hdes". iDestruct "Hdes" as (v' ps1) "(AuthLoc1 & AuthVal1 & %Hstep & #Hvv')".
    iEval (rewrite valrel_typed_TArrow_unfold) in "Hv2v2'". iSpecialize ("Hv2v2'" $! v v' with "Hvv'").
    iApply (wp_bind (fill [RunSTCtx])). iApply (wp_wand with "Hv2v2'").
    iIntros (s) "Hdes". iDestruct "Hdes" as (s') "(%Hstep' & #Hss')". simpl.
    iEval (rewrite valrel_typed_TST_unfold) in "Hss'". rewrite eq. iSpecialize ("Hss'" $! ps1 with "[AuthLoc1 AuthVal1]"); iFrame.
    iApply (wp_wand with "Hss'"). iIntros (r) "Hdes". iDestruct "Hdes" as (r' ps2) "(AuthLoc2 & AuthVal2 & %Hstep'' & #Hrr')".
    iExists r', ps2. iFrame. iFrame "Hrr'". iPureIntro.
    by eapply bind_v_f_step.
  Qed.

  Lemma compat_retrn Γ e e' ρ τ :
    open_exprel_typed Γ e e' τ →
    open_exprel_typed Γ (Return e) (retrn e') (TST ρ τ).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Hee' Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    change (retrn ?e).[?σ] with (retrn e.[σ]).
    iApply (lift_bind _ [ReturnCtx] [STLCmuVS.lang.AppRCtx _] with "Hee'").
    simpl. iIntros (v v') "#Hvv'". iClear "Hee'".
    iApply lift_step. apply head_prim_step. econstructor. by rewrite STLCmuVS.lang.to_of_val. asimpl.
    change (Return (of_val ?v)) with (of_val $ ReturnV v). change (STLCmuVS.lang.Lam ?e) with (STLCmuVS.lang.of_val $ STLCmuVS.lang.LamV e).
    iApply lift_val.
    (* ok *)
    rewrite valrel_typed_TST_unfold. destruct ρ; auto. destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
    iIntros (ps). iModIntro. iIntros "[AuthLoc AuthVal]". iApply wp_pure_step_later. apply pure_step_RunST_Return_val. iNext. iApply wp_value'.
    iExists v', ps. iFrame. iFrame "Hvv'". iPureIntro.
    apply rtc_once. apply head_prim_step. eapply App_Lam_head_step'. by asimpl.
    by rewrite STLCmuVS.lang.to_of_val.
  Qed.

  Lemma compat_runst Γ e e' τ :
    open_exprel_typed (subst (ren (+1)) <$> Γ) e e' (TST (TVar 0) τ.[ren (+1)]) →
    open_exprel_typed Γ (RunST e) (runst e') τ.
  Proof.
    iIntros (Hee' Δ vs vs') "#Hvsvs'".
    change (runst ?e).[?σ] with (runst e.[σ]). simpl.
    iDestruct (@ghost_empty _ loc) as "#Hγ". iDestruct (@ghost_empty _ STLCmuVS.lang.val) as "#Hγ'".
    iMod "Hγ" as (γ) "AuthLoc". iMod "Hγ'" as (γ') "AuthVal".
    specialize (Hee' ((γ, γ') :: Δ) vs vs').
    iDestruct Hee' as "Hee'". clear Hee'.
    rewrite -big_sepL3_fmap_l.
    (* change (Lam ?e) with (of_val $ LamV e). *)
    iApply (@wp_bind _ _ _ (fill_item $ RunSTCtx) (ectxi_lang_ctx_item _)).
    iApply wp_wand. iApply "Hee'". iApply (big_sepL3_impl with "Hvsvs'"). iModIntro. iIntros (τ' v v') "H". by iApply valrel_typed_cons_ren. iEval simpl.
    iIntros (v) "H". iDestruct "H" as (v') "[%Hsteps #Hvv']". iClear "Hvsvs' Hee'".
    rewrite valrel_typed_TST_unfold /=. iSpecialize ("Hvv'" $! [] with "[AuthLoc AuthVal]"). iFrame.
    iApply (wp_wand with "Hvv'"). iIntros (w) "Hdes". iDestruct "Hdes" as (w' psf) "(AuthLoc & AuthVal & %Hsteps' & #Hrr')".
    iExists w'. iSplit. iPureIntro.
    change (STLCmuVS.lang.Lam ?e) with (STLCmuVS.lang.of_val (STLCmuVS.lang.LamV e)).
    eapply rtc_transitive.
    by apply (@rtc_STLCmuVS_step_ctx (STLCmuVS.lang.fill_item $ STLCmuVS.lang.AppRCtx _) (ectxi_lang_ctx_item _)). simpl.
    eapply rtc_l. apply head_prim_step. econstructor. by rewrite STLCmuVS.lang.to_of_val. asimpl. rewrite encode_empty_subst.
    eapply rtc_transitive.
    by apply (@rtc_STLCmuVS_step_ctx (STLCmuVS.lang.fill_item $ STLCmuVS.lang.SndCtx) (ectxi_lang_ctx_item _)). simpl.
    change (STLCmuVS.lang.Pair (STLCmuVS.lang.of_val ?v1) (STLCmuVS.lang.of_val ?v2)) with (STLCmuVS.lang.of_val (STLCmuVS.lang.PairV v1 v2)).
    apply rtc_once. apply head_prim_step. econstructor. fold STLCmuVS.lang.of_val. by rewrite STLCmuVS.lang.to_of_val. by rewrite STLCmuVS.lang.to_of_val.
    by iApply valrel_typed_cons_ren.
  Qed.

  Lemma compat_compare Γ e1 e1' e2 e2' ρ τ :
    open_exprel_typed Γ e1 e1' (TSTref ρ τ) →
    open_exprel_typed Γ e2 e2' (TSTref ρ τ) →
    open_exprel_typed Γ (Compare e1 e2)%Eₛₜ (e1' = e2')%Eₙₒ TBool.
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (H1 H2 Δ vs vs') "#Hvsvs'".
    specialize (H1 Δ vs vs'). specialize (H2 Δ vs vs').
    iDestruct (H1 with "Hvsvs'") as "H1". clear H1. iDestruct (H2 with "Hvsvs'") as "H2". clear H2.
    iClear "Hvsvs'". iEval simpl.
    iApply (lift_bind _ [CompLCtx _] [STLCmuVS.lang.BinOpLCtx _ _] with "H1"). iEval simpl.
    iIntros (v1 v1') "#Hv1v1'". iClear "H1".
    iApply (lift_bind _ [CompRCtx _] [STLCmuVS.lang.BinOpRCtx _ _] with "H2"). iEval simpl.
    iIntros (v2 v2') "#Hv2v2'". simpl. iClear "H2".
    (* okay *)
    rewrite !valrel_typed_TSTRef_unfold. destruct ρ; auto; destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
    iDestruct "Hv1v1'" as (i1 l1) "(-> & Hl1 & -> & Hinv1)".
    iDestruct "Hv2v2'" as (i2 l2) "(-> & Hl2 & -> & Hinv2)".

    iApply lift_step. apply head_prim_step. econstructor; by rewrite STLCmuVS.lang.to_of_val.
    iApply lift_pure_step_later. apply pure_step_eq_loc. iNext. iApply lift_val_fupd.
    setoid_rewrite valrel_typed_TBool_unfold.
    iExists (bool_decide (l1 = l2)). iSplitL ""; auto.
    destruct (decide (i1 = i2)) as [<- | neq].
    - iDestruct (ghost_map_elem_agree with "Hl1 Hl2") as "->".
      by rewrite /= !bool_decide_eq_true_2.
    - iInv "Hinv1" as (w1 w1') "(>Hi1 & >Hl1' & #Hww1')" "Hclose1".
      iInv "Hinv2" as (w2 w2') "(>Hi2 & >Hl2' & #Hww2')" "Hclose2".
      iDestruct (mapsto_frac_ne with "Hl1' Hl2'") as "%neq'"; auto.
      iApply (fupd_trans _ (difference top (↑nroot.@γ.@γ'.@i1)) top).
      iApply fupd_wand_r. iSplitL "Hclose2 Hi2 Hl2'". iApply "Hclose2". iNext. iExists w2, w2'. by iFrame.
      iIntros "_".
      iApply fupd_wand_r. iSplitL "Hclose1 Hi1 Hl1'". iApply "Hclose1". iNext. iExists w1, w1'. by iFrame.
      iIntros "_".
      iPureIntro.
      rewrite /= !bool_decide_eq_false_2; auto. lia.
  Qed.

End compat_lemmas.
