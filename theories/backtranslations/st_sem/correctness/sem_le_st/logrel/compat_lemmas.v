From iris.program_logic Require Import weakestpre lifting ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.

Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

From st.prelude Require Import big_op_three.

From st.lamst Require Import lang types typing.

From st.lam Require Import lang wkpre tactics.
From st.backtranslations.st_sem Require Import help expressions ghost heap_emul.base heap_emul.spec.
From st.backtranslations.st_sem.correctness.sem_le_st.logrel Require Import lift definition compat_help.
From st Require Import resources.

Section compat_lemmas.

  Context `{Σ : !gFunctors} `{sem_le_stΣ_inst : !sem_le_stΣ Σ}.

  Opaque alloc alloc_v encode.

  Lemma compat_alloc Γ e e' ρ τ (Hee' : open_exprel_typed Γ e e' τ) :
    open_exprel_typed Γ (alloc e) (Alloc e') (TST ρ (TSTref ρ τ)).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    rewrite /= !alloc_Closed.
    iApply (lift_bind _ [AppRCtx _] [AllocCtx]  with "Hee'"). iClear "Hee'".
    iIntros (v v') "#Hvv'". simpl.
    (* ok *)
    iApply lift_step_later. apply alloc_step.
    change (Alloc v') with (lamst.lang.of_val (AllocV v')). iApply lift_val.
    rewrite valrel_typed_TST_unfold. destruct ρ; auto. destruct (Δ !! X) as [[γ γ']|]eqn:eq; auto.
    (*  *)
    iIntros (psᵢ σ). do 2 iModIntro. iIntros "Hσ AuthVals AuthLocs".
    iApply wp_rtc_steps. apply alloc_v_steps.
    change (Lit ?b) with (of_val (LitV b)).
    change ((of_val ?v1, of_val ?v2)%Eₙₒ) with (of_val (v1, v2)%Vₙₒ).
    iApply wp_value_fupd'.
    iMod (gen_heap_alloc σ (fresh_loc σ) v' (fresh_loc_lookup_None σ) with "Hσ") as "(Hσ' & Hfreshv' & _)".
    iMod ((ghost_alloc_persist γ' psᵢ.*2 (fresh_loc σ)) with "AuthLocs") as "[AuthLocsFin #Hloc]".
    iMod ((ghost_alloc γ psᵢ.*1 v) with "AuthVals") as "[AuthValsFin Hval]".
    iExists (length psᵢ.*1), (fresh_loc σ), (psᵢ ++ [(v,fresh_loc σ)]), (<[fresh_loc σ:=v']> σ).
    rewrite !fmap_app /=. iFrame. iSplitL ""; auto.
    iSplitL "".
    { iPureIntro.
      apply rtc_l with (y := (<[fresh_loc σ:=v']> σ, RunST (Return (fresh_loc σ)))).
      apply head_prim_step. constructor.
      apply head_prim_step. constructor. by apply fresh_loc_lookup_None. by rewrite lang.to_of_val.
      apply rtc_once.
      apply head_prim_step. by econstructor.
    }
    rewrite valrel_typed_TSTRef_unfold eq.
    iExists _, _; do 2 (iSplitL ""; auto).
    iApply fupd_frame_l. rewrite !fmap_length. iFrame "Hloc".
    iApply inv_alloc. iNext. iExists v, v'. by iFrame.
  Qed.

  Opaque read read_i.

  Lemma compat_read Γ e e' ρ τ :
    open_exprel_typed Γ e e' (TSTref ρ τ) →
    open_exprel_typed Γ (read e) (Read e') (TST ρ τ).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Hee' Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    rewrite /= !read_Closed.
    iApply (lift_bind _ [AppRCtx _] [ReadCtx] with "Hee'").
    simpl. iIntros (v v') "#Hvv'". iClear "Hee'".
    rewrite valrel_typed_TSTRef_unfold. destruct ρ; auto. destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
    iDestruct "Hvv'" as (i l) "(-> & -> & Hloc & #HInv)".
    (* steps *)
    iApply lift_step_later. apply read_step. iNext.
    change (lamst.lang.Lit l) with (lamst.lang.of_val l). change (Read (lang.of_val l)) with (lang.of_val (ReadV l)).
    (* okay *)
    iApply lift_val.
    rewrite valrel_typed_TST_unfold. rewrite eq.
    iIntros (psᵢ σ). iModIntro. iIntros "Hσ AuthVals AuthLocs". iApply fupd_wp.
    iInv "HInv" as (w w') "(>Hiγ'w' & >Hlw & #Hww)" "HClose".
    iDestruct (gen_heap_valid with "Hσ Hlw") as "%H".
    iDestruct (ghost_read with "AuthVals Hiγ'w'") as "%H'".
    iApply fupd_wand_r. iSplitL "HClose Hiγ'w' Hlw". iApply "HClose". iNext. iExists _, _. by iFrame.
    iIntros (_).
    iApply wp_at_least_one_later. by apply read_i_at_least_one. iNext.
    iApply wp_value'. iExists w, w', psᵢ, σ. iFrame. repeat iSplitL ""; auto.
    { iPureIntro.
      apply rtc_l with (y := (σ, RunST (Return w'))).
      apply head_prim_step. constructor.
      apply head_prim_step. by constructor.
      apply rtc_once.
      apply head_prim_step. econstructor. by rewrite lang.to_of_val.
    }
  Qed.

  Lemma compat_write Γ e1 e1' e2 e2' ρ τ :
    open_exprel_typed Γ e1 e1' (TSTref ρ τ) →
    open_exprel_typed Γ e2 e2' τ →
    open_exprel_typed Γ (write e1 e2) (Write e1' e2') (TST ρ TUnit).
  Proof.
    Local Opaque write write_i write_i_v.
    (* cleaning and getting to the gist of it *)
    iIntros (H1 H2 Δ vs vs') "#Hvsvs'".
    specialize (H1 Δ vs vs'). specialize (H2 Δ vs vs').
    iDestruct (H1 with "Hvsvs'") as "H1". clear H1. iDestruct (H2 with "Hvsvs'") as "H2". clear H2.
    iClear "Hvsvs'".
    change ((write ?e1 ?e2).[?σ]) with (write e1.[σ] e2.[σ]).
    iApply (lift_bind _ [lam.lang.AppRCtx _; lam.lang.AppLCtx _] [WriteLCtx _] with "H1"). simpl.
    iIntros (v1 v1') "#Hv1v1'". iClear "H1".
    iApply lift_step_later.
    apply (@lam_step_ctx (lam.lang.fill_item (lam.lang.AppLCtx _)) (ectxi_lang_ctx_item _)). apply write_step. simpl.
    iApply (lift_bind _ [lam.lang.AppRCtx _] [WriteRCtx _] with "H2"). iClear "H2". iNext.
    iIntros (v2 v2') "#Hv2v2'". simpl.
    iApply lift_step_later. apply write_i_step. iNext.
    change (Write v1' v2') with (lang.of_val $ WriteV v1' v2').
    iApply lift_val.
    (* okay *)
    iEval (rewrite valrel_typed_TSTRef_unfold) in "Hv1v1'".
    rewrite valrel_typed_TST_unfold; destruct ρ; auto; destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
    iDestruct "Hv1v1'" as (i l) "(-> & -> & Hil & HInv)".
    iIntros (psᵢ σ). iModIntro. iIntros "Hσ AuthVals AuthLocs".
    iApply fupd_wp.
    iInv "HInv" as (w w') "(>Hiγ'w' & >Hlw & #Hww)" "HClose".
    iDestruct (gen_heap_valid with "Hσ Hlw") as "%H".
    iDestruct (ghost_read with "AuthVals Hiγ'w'") as "%H'".
    iApply fupd_wand_r. iSplitL "HClose Hiγ'w' Hlw". iApply "HClose". iNext. iExists _, _. by iFrame. iIntros (_).
    iApply wp_at_least_one_step_fupd. by eapply write_i_v_at_least_one.
    iInv "HInv" as (x x') "(>Hiγx & >Hlx' & #Hxx)" "HClose".
    iMod (ghost_write γ psᵢ.*1 x i v2 with "AuthVals Hiγx") as "[AuthVals Hiγv2]".
    iMod (gen_heap_update σ l x' v2' with "Hσ Hlx'") as "[Hσ' Hlv2']".
    iApply fupd_wand_r. iSplitL "HClose". iApply "HClose".
    iIntros "H". iNext.
    iApply fupd_wand_r. iSplitL "H Hiγv2 Hlv2'". iApply "H". iNext. iExists _, _. by iFrame.
    iIntros (_).
    iApply wp_value'.
    setoid_rewrite valrel_typed_TUnit_unfold.
    iExists _, _, (zip (<[i := v2]> psᵢ.*1) psᵢ.*2), _.
    rewrite fst_zip; [|by rewrite insert_length !fmap_length].
    rewrite snd_zip; [|by rewrite insert_length !fmap_length]. iFrame.
    repeat iSplitL ""; auto.
    { iPureIntro.
      apply rtc_l with (y := (<[l := v2']>σ, RunST (Return ()%Vₛₜ))).
      apply head_prim_step. constructor.
      apply head_prim_step. constructor. by eexists. by rewrite lang.to_of_val.
      apply rtc_once.
      apply head_prim_step. econstructor. by simpl.
    }
  Qed.

  Opaque bind bind_v.

  Lemma compat_bind Γ e1 e1' e2 e2' ρ τ1 τ2 :
    open_exprel_typed Γ e1 e1' (TST ρ τ1) →
    open_exprel_typed Γ e2 e2' (τ1 ⟶ TST ρ τ2)%Tₛₜ →
    open_exprel_typed Γ (bind e1 e2) (Bind e1' e2') (TST ρ τ2).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (H1 H2 Δ vs vs') "#Hvsvs'".
    specialize (H1 Δ vs vs'). specialize (H2 Δ vs vs').
    iDestruct (H1 with "Hvsvs'") as "H1". clear H1. iDestruct (H2 with "Hvsvs'") as "H2". clear H2.
    iClear "Hvsvs'".
    change ((bind ?e1 ?e2).[?σ]) with (bind e1.[σ] e2.[σ]).
    change ((Bind ?e1 ?e2).[?σ]) with (Bind e1.[σ] e2.[σ]).
    iApply (lift_bind _ [lam.lang.AppRCtx _; lam.lang.AppLCtx _] [BindLCtx _] with "H1"). simpl.
    iIntros (v1 v1') "#Hv1v1'". iClear "H1".
    iApply lift_step_later. apply (@lam_step_ctx (lam.lang.fill_item (lam.lang.AppLCtx _)) (ectxi_lang_ctx_item _)). apply bind_step. iNext. simpl.
    iApply (lift_bind _ [lam.lang.AppRCtx _] [BindRCtx _] with "H2").
    iIntros (v2 v2') "#Hv2v2'". simpl.
    iApply lift_step_later. apply bind_v_step. iNext.
    change (Bind (lang.of_val ?v1) (lang.of_val ?v2)) with (lang.of_val $ BindV v1 v2).
    iApply lift_val.
    (* okay *)
    iEval (rewrite valrel_typed_TST_unfold) in "Hv1v1'".
    iEval (rewrite valrel_typed_TST_unfold). destruct ρ; auto. destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
    iIntros (ps0 σ0). iModIntro. iIntros "Hσ0 AuthVal0 AuthLoc0".
    iSpecialize ("Hv1v1'" $! ps0 σ0 with "Hσ0 AuthVal0 AuthLoc0").
    rewrite /bind_v_f. iApply wp_step_later.
    { apply head_prim_step. eapply App_Lam_head_step'. asimpl. eauto. by rewrite to_of_val. } iNext.
    iApply (wp_bind' [LetInCtx _]).
    iApply (wp_wand with "Hv1v1'"). simpl.
    iIntros (v) "Hdes". iDestruct "Hdes" as (w w' ps1 σ1) "(-> & Hσ1 & AuthVal1 & AuthLoc1 & %Hstep & #Hww')".
    iApply wp_step_later.
    { apply head_prim_step. econstructor. by rewrite to_of_val. } iNext. asimpl.
    iApply wp_step_later.
    { eapply (@lam_step_ctx (fill [LetInCtx _]) (ectx_lang_ctx _)).
      apply head_prim_step. econstructor; by rewrite to_of_val. } simpl.
    iApply wp_step_later.
    { apply head_prim_step. econstructor. by rewrite to_of_val. } iNext. iNext. asimpl.
    iApply wp_step_later.
    { eapply (@lam_step_ctx (fill [LetInCtx _]) (ectx_lang_ctx _)).
      apply head_prim_step. econstructor; by rewrite to_of_val. } asimpl. iNext.
    iApply wp_step_later.
    { apply head_prim_step. econstructor. by rewrite to_of_val. } iNext. asimpl.
    iEval (rewrite valrel_typed_TArrow_unfold /lift) in "Hv2v2'".
    iSpecialize ("Hv2v2'" $! w w' with "Hww'").
    iSpecialize ("Hv2v2'" $! σ1 with "Hσ1").
    iApply (wp_bind' [AppLCtx _]). iApply (wp_wand with "Hv2v2'").
    iIntros (s) "Hdes". iDestruct "Hdes" as (s' σ2) "(Hσ2 & %Hstep' & #Hss')". simpl.
    iEval (rewrite valrel_typed_TST_unfold eq) in "Hss'".
    iSpecialize ("Hss'" $! ps1 σ2 with "Hσ2 AuthVal1 AuthLoc1").
    iApply (wp_wand with "Hss'").
    iIntros (y) "Hdes". iDestruct "Hdes" as (r r' ps2 σ3) "(-> & Hσ3 & AuthLoc2 & AuthVal2 & %Hstep'' & #Hrr')".
    iExists r, r', ps2, σ3. iFrame. iSplit; auto. iSplit; auto. iPureIntro. by eapply rtc_bind_lemma.
  Qed.

  Lemma compat_retrn Γ e e' ρ τ :
    open_exprel_typed Γ e e' τ →
    open_exprel_typed Γ (retrn e) (Return e') (TST ρ τ).
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (Hee' Δ vs vs') "#Hvsvs'".
    specialize (Hee' Δ vs vs').
    iDestruct (Hee' with "Hvsvs'") as "Hee'". clear Hee'. iClear "Hvsvs'".
    change (Return ?e).[?σ] with (Return e.[σ]).
    change (retrn ?e).[?σ] with (retrn e.[σ]).
    iApply (lift_bind _ [lam.lang.AppRCtx _] [ReturnCtx] with "Hee'").
    simpl. iIntros (v v') "#Hvv'". iClear "Hee'".
    iApply lift_step_later. apply head_prim_step. econstructor. by rewrite lam.lang.to_of_val. asimpl.
    change (Return (lang.of_val ?v)) with (lang.of_val $ ReturnV v). change (lam.lang.Lam ?e) with (lam.lang.of_val $ lam.lang.LamV e).
    iApply lift_val.
    (* ok *)
    rewrite valrel_typed_TST_unfold. destruct ρ; auto. destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
    iIntros (ps σ). do 2 iModIntro. iIntros "Hσ AuthLoc AuthVal".
    iApply wp_step_later. apply head_prim_step. eapply App_Lam_head_step'. by asimpl. by rewrite lam.lang.to_of_val. iNext.
    change ((of_val ?v1, of_val ?v2)%Eₙₒ) with (of_val (v1, v2)%Vₙₒ). iApply wp_value'.
    iExists v, v', ps, σ. iFrame. iFrame "Hvv'".
    iSplit; auto. iPureIntro. apply rtc_once. apply head_prim_step. econstructor. by rewrite lang.to_of_val.
  Qed.

  (* Opaque runst. *)

  Lemma compat_runst Γ e e' τ :
    open_exprel_typed (subst (ren (+1)) <$> Γ) e e' (TST (TVar 0) τ.[ren (+1)]) →
    open_exprel_typed Γ (runst e) (RunST e') τ.
  Proof.
    iIntros (Hee' Δ vs vs') "#Hvsvs'".
    change (runst ?e).[?σ] with (runst e.[σ]).
    change (RunST ?e).[?σ] with (RunST e.[σ]).
    iIntros (σ) "Hσ".
    iMod (@ghost_empty _ lam.lang.val) as (γ) "AuthVals". iMod (@ghost_empty _ loc) as (γ') "AuthLocs".
    iDestruct (Hee' ((γ, γ') :: Δ) vs vs') as "Hee'". clear Hee'.
    rewrite -big_sepL3_fmap_l.
    (* change (Lam ?e) with (of_val $ LamV e). *)
    iApply (wp_bind' [AppRCtx _]).
    iApply (wp_wand with "[Hσ]"). iApply "Hee'"; auto. iApply (big_sepL3_impl with "Hvsvs'"). iModIntro. iIntros (τ' v v') "H". by iApply valrel_typed_cons_ren.
    iIntros (v) "H". iDestruct "H" as (v' σ') "(Hσ' & %Hsteps & #Hvv')". iClear "Hvsvs' Hee'". simpl.
    rewrite valrel_typed_TST_unfold /=. iSpecialize ("Hvv'" $! [] σ' with "Hσ' AuthVals AuthLocs").
    iApply wp_step_later. apply head_prim_step. econstructor. by rewrite lam.lang.to_of_val. asimpl. iNext. rewrite encode_empty_subst.
    iApply (wp_bind' [SndCtx]).
    iApply (wp_wand with "Hvv'"). simpl. iIntros (x) "Hdes". iDestruct "Hdes" as (w w' ps σ'') "(-> & Hσ'' & AuthVals & AuthLocs & %Hsteps' & #Hrr')".
    iApply wp_step_later. apply head_prim_step. econstructor; fold of_val; by rewrite lam.lang.to_of_val. fold of_val. iNext.
    iApply wp_value'. iExists w', σ''. iFrame. iSplit.
    iPureIntro. eapply rtc_transitive; eauto. by apply (fill_lamst_step_rtc [RunSTCtx]).
    by iApply valrel_typed_cons_ren.
  Qed.

  Lemma compat_compare Γ e1 e1' e2 e2' ρ τ :
    open_exprel_typed Γ e1 e1' (TSTref ρ τ) →
    open_exprel_typed Γ e2 e2' (TSTref ρ τ) →
    open_exprel_typed Γ (e1 = e2)%Eₙₒ (Compare e1' e2')%Eₛₜ TBool.
  Proof.
    (* cleaning and getting to the gist of it *)
    iIntros (H1 H2 Δ vs vs') "#Hvsvs'".
    specialize (H1 Δ vs vs'). specialize (H2 Δ vs vs').
    iDestruct (H1 with "Hvsvs'") as "H1". clear H1. iDestruct (H2 with "Hvsvs'") as "H2". clear H2.
    iClear "Hvsvs'". iEval simpl.
    iApply (lift_bind _ [BinOpLCtx _ _] [CompLCtx _] with "H1"). iEval simpl.
    iIntros (v1 v1') "#Hv1v1'". iClear "H1".
    iApply (lift_bind _ [BinOpRCtx _ _] [CompRCtx _] with "H2"). iEval simpl.
    iIntros (v2 v2') "#Hv2v2'". simpl. iClear "H2".
    (* okay *)
    rewrite !valrel_typed_TSTRef_unfold. destruct ρ; auto; destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
    iDestruct "Hv1v1'" as (i1 l1) "(-> & -> & Hl1 & Hinv1)".
    iDestruct "Hv2v2'" as (i2 l2) "(-> & -> & Hl2 & Hinv2)".
    iApply lift_step_later. apply head_prim_step. econstructor; by rewrite lam.lang.to_of_val.
    iApply lift_pure_step. apply pure_step_eq_loc. iNext. iApply lift_val_fupd.
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
