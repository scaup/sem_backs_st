From iris.program_logic Require Import language ectxi_language ectx_language lifting.
From st.STLCmu Require Import lang.

Definition STLCmu_head_step (e e' : expr) := head_step e tt [] e' tt [].

Lemma head_to_STLCmu_head (e e' : expr) σ σ' κ efs : head_step e σ κ e' σ' efs → STLCmu_head_step e e'.
Proof. intro H. rewrite /STLCmu_head_step. inversion H; by econstructor. Qed.

Definition STLCmu_reducible (e : expr) := ∃ e', STLCmu_step e e'.
Definition STLCmu_irreducible (e : expr) := ∀ e', ¬ STLCmu_step e e'.
Definition STLCmu_head_reducible (e : expr) := ∃ e', STLCmu_head_step e e'.
Definition STLCmu_head_irreducible (e : expr) := ∀ e', ¬ STLCmu_head_step e e'.

Lemma prim_to_STLCmu (e1 e2 : expr) σ1 σ2 κ efs : prim_step e1 σ1 κ e2 σ2 efs -> STLCmu_step e1 e2.
Proof. intro H. apply STLCmu_pure. apply (prim_step_pure _ _ _ _ _ _ H). Qed.

Lemma STLCmu_prim_red (e : expr) : STLCmu_reducible e <-> reducible e tt.
Proof.
  split. intro H. destruct H as [e' Hstep]. exists [], e', tt, []. apply Hstep.
  intro H. destruct H as (a & e' & b & c & Hstep). exists e'. by eapply prim_to_STLCmu.
Qed.
Lemma STLCmu_prim_irred (e : expr) : STLCmu_irreducible e <-> irreducible e tt.
Proof.
  split.
  + rewrite /STLCmu_irreducible /irreducible.
    intros. intro abs. apply (H e'). by eapply prim_to_STLCmu.
  + intros H e' abs. rewrite /irreducible in H. by apply (H [] e' () []).
Qed.
Lemma STLCmu_prim_head_red (e : expr) : STLCmu_head_reducible e <-> head_reducible e tt.
Proof.
  split. intro H. destruct H as [e' Hstep]. exists [], e', tt, []. apply Hstep.
  intro H. destruct H as (a & e' & b & c & Hstep). exists e'. destruct Hstep; by econstructor.
Qed.
Lemma STLCmu_prim_head_irred (e : expr) : STLCmu_head_irreducible e <-> head_irreducible e tt.
Proof.
  split. intro H. intros κ e' σ efs abs. apply (H e'). by eapply head_to_STLCmu_head.
  intros H e' Hstep. apply (H [] e' () []). auto.
Qed.

Lemma stuck_no_val_irred e : (to_val e = None) → stuck e tt → irreducible e tt.
Proof. rewrite /stuck. intuition. Qed.

(* Ltac head_stuck_solver := *)
(*   lazymatch goal with *)
(*   | |- stuck ?e () => apply head_stuck_stuck; head_stuck_solver *)
(*   | |- head_stuck ?e () => split; head_stuck_solver *)
(*   | |- rtc STLCmu_step _ _ => (eapply rtc_l; first (auto_STLCmu_step); simplify_custom) *)
(*   | |- ectx_language.to_val _ = _ => (by simplify_custom) ; head_stuck_solver *)
(*   | |- head_irreducible _ () => ((apply STLCmu_prim_head_irred; intros e' abs; inversion abs; simplify_option_eq); try done); head_stuck_solver *)
(*   | |- sub_redexes_are_values _ => apply ectxi_language_sub_redexes_are_values; intros Ki' e' eqqq; destruct Ki'; inversion eqqq; head_stuck_solver *)
(*   | |- is_Some _ => (by eexists; simplify_custom) ; head_stuck_solver *)
(*   | |- _ => auto *)
(*   end. *)

(* Inductive reducibility (e : expr) : Type := *)
(*   | is_val v : to_val e = Some v → reducibility e *)
(*   | is_red : reducible e tt → reducibility e *)
(*   | is_stuck : stuck e tt → reducibility e. *)

(* Lemma fill_stuck (K : list ectx_item) (e : expr) : *)
(*     stuck e tt → stuck (fill K e) tt. *)
(* Proof. apply stuck_fill. Qed. *)

(* Lemma dec_expr_reducibility (e : expr) : reducibility e. *)
(* Proof. *)
(*   induction e as [x | e1 IH1 e2 IH2 | e _ | e1 IH1 e2 IH2 | | op e1 IH1 e2 IH2 | e0 IH0 e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH | e IH | e IH | e IH | e0 IH0 e1 IH1 e2 IH2 | e IH | e IH | e IH ]; *)
(*     (try by eapply is_val). *)
(*   - apply is_stuck. head_stuck_solver. *)
(*   - destruct IH1 as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + apply is_red; apply STLCmu_prim_red; eexists; auto_STLCmu_step. *)
(*     + apply is_red; by apply (fill_reducible [LetInCtx _]). *)
(*     + apply is_stuck; by apply (fill_stuck [LetInCtx _]). *)
(*   - destruct IH1 as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + destruct IH2 as [ v2 eq2 | is_red2 | is_stuck2 ]; [ rewrite -(of_to_val _ _ eq2) | | ]. *)
(*       * destruct v1; try by (apply is_stuck; head_stuck_solver). *)
(*         apply is_red; apply STLCmu_prim_red; eexists; auto_STLCmu_step. *)
(*       * apply is_red; by apply (fill_reducible [AppRCtx _]). *)
(*       * apply is_stuck; by apply (fill_stuck [AppRCtx _]). *)
(*     + apply is_red; by apply (fill_reducible [AppLCtx _]). *)
(*     + apply is_stuck; by apply (fill_stuck [AppLCtx _]). *)
(*   - destruct IH1 as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + destruct IH2 as [ v2 eq2 | is_red2 | is_stuck2 ]; [ rewrite -(of_to_val _ _ eq2) | | ]. *)
(*       * destruct v1; (lazymatch goal with | v : base_lit |- _ => destruct v | |- _ => auto end); try by (apply is_stuck; head_stuck_solver). *)
(*         destruct v2; (lazymatch goal with | v : base_lit |- _ => destruct v | |- _ => auto end); try by (apply is_stuck; head_stuck_solver). *)
(*         apply is_red; apply STLCmu_prim_red; eexists; auto_STLCmu_step. *)
(*       * apply is_red; by apply (fill_reducible [BinOpRCtx _ _]). *)
(*       * apply is_stuck; by apply (fill_stuck [BinOpRCtx _ _]). *)
(*     + apply is_red; by apply (fill_reducible [BinOpLCtx _ _]). *)
(*     + apply is_stuck; by apply (fill_stuck [BinOpLCtx _ _]). *)
(*   - destruct IH0 as [ v0 eq0 | is_red0 | is_stuck0 ]; [ rewrite -(of_to_val _ _ eq0) | | ]. *)
(*     + destruct v0; (lazymatch goal with | v : base_lit |- _ => destruct v | |- _ => auto end); try by (apply is_stuck; head_stuck_solver). *)
(*       destruct b; apply is_red; apply STLCmu_prim_red; eexists; auto_STLCmu_step. *)
(*     + apply is_red; by apply (fill_reducible [IfCtx _ _]). *)
(*     + apply is_stuck; by apply (fill_stuck [IfCtx _ _]). *)
(*   - destruct IH1 as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + destruct v1; (lazymatch goal with | v : base_lit |- _ => destruct v | |- _ => auto end); try by (apply is_stuck; head_stuck_solver). *)
(*       apply is_red; apply STLCmu_prim_red; eexists; auto_STLCmu_step. *)
(*     + apply is_red; by apply (fill_reducible [SeqCtx _]). *)
(*     + apply is_stuck; by apply (fill_stuck [SeqCtx _]). *)
(*   - destruct IH1 as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + destruct IH2 as [ v2 eq2 | is_red2 | is_stuck2 ]; [ rewrite -(of_to_val _ _ eq2) | | ]. *)
(*       * by apply (is_val _ (v1, v2)%Vₙₒ); simplify_custom. *)
(*       * apply is_red; by apply (fill_reducible [PairRCtx _]). *)
(*       * apply is_stuck; by apply (fill_stuck [PairRCtx _]). *)
(*     + apply is_red; by apply (fill_reducible [PairLCtx _]). *)
(*     + apply is_stuck; by apply (fill_stuck [PairLCtx _]). *)
(*   - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + destruct v1; try by (apply is_stuck; head_stuck_solver). *)
(*       apply is_red; apply STLCmu_prim_red; eexists; auto_STLCmu_step. *)
(*     + apply is_red. by apply (fill_reducible [FstCtx]). *)
(*     + apply is_stuck; by apply (fill_stuck [FstCtx]). *)
(*   - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + destruct v1; try by (apply is_stuck; head_stuck_solver). *)
(*       apply is_red; apply STLCmu_prim_red; eexists; auto_STLCmu_step. *)
(*     + apply is_red. by apply (fill_reducible [SndCtx]). *)
(*     + apply is_stuck; by apply (fill_stuck [SndCtx]). *)
(*   - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + apply (is_val _ (InjLV v1)). by simplify_custom. *)
(*     + apply is_red. by apply (fill_reducible [InjLCtx]). *)
(*     + apply is_stuck; by apply (fill_stuck [InjLCtx]). *)
(*   - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + apply (is_val _ (InjRV v1)). by simplify_custom. *)
(*     + apply is_red. by apply (fill_reducible [InjRCtx]). *)
(*     + apply is_stuck; by apply (fill_stuck [InjRCtx]). *)
(*   - destruct IH0 as [ v0 eq0 | is_red0 | is_stuck0 ]; [ rewrite -(of_to_val _ _ eq0) | | ]. *)
(*     + (destruct v0; try by (apply is_stuck; head_stuck_solver)); *)
(*       apply is_red; apply STLCmu_prim_red; eexists; auto_STLCmu_step. *)
(*     + apply is_red; by apply (fill_reducible [CaseCtx _ _]). *)
(*     + apply is_stuck; by apply (fill_stuck [CaseCtx _ _]). *)
(*   - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + apply (is_val _ (FoldV v1)). by simplify_custom. *)
(*     + apply is_red. by apply (fill_reducible [FoldCtx]). *)
(*     + apply is_stuck; by apply (fill_stuck [FoldCtx]). *)
(*   - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + destruct v1; try by (apply is_stuck; head_stuck_solver). *)
(*       apply is_red; apply STLCmu_prim_red; eexists; auto_STLCmu_step. *)
(*     + apply is_red. by apply (fill_reducible [UnfoldCtx]). *)
(*     + apply is_stuck; by apply (fill_stuck [UnfoldCtx]). *)
(*   - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ]. *)
(*     + destruct v1; apply is_red; apply STLCmu_prim_red; eexists; auto_STLCmu_step. *)
(*     + apply is_red. by apply (fill_reducible [VirtStepCtx]). *)
(*     + apply is_stuck; by apply (fill_stuck [VirtStepCtx]). *)
(* Qed. *)

Inductive Reducible : expr → Prop :=
  | LetIn_L_Red e1 e2 : Reducible e1 → Reducible (LetIn e1 e2)
  | LetIn_D_Red e1 v1 e2 : to_val e1 = Some v1 → Reducible (LetIn e1 e2)
  | App_L_Red e1 e2 : Reducible e1 → Reducible (App e1 e2)
  | App_R_Red e1 v1 e2 : to_val e1 = Some v1 → Reducible e2 → Reducible (App e1 e2)
  | App_D_Red e1 e2 v2 : to_val e2 = Some v2 → Reducible (App (Lam e1) e2)
  | BinOp_L_Red op e1 e2 : Reducible e1 → Reducible (BinOp op e1 e2)
  | BinOp_R_Red op e1 v1 e2 : to_val e1 = Some v1 → Reducible e2 → Reducible (BinOp op e1 e2)
  | BinOp_D_Red op z1 z2 : Reducible (BinOp op (Lit (LitInt z1)) (Lit (LitInt z2)))
  | If_C_Red e e1 e2 : Reducible e → Reducible (If e e1 e2)
  | If_D_Red b e1 e2 : Reducible (If (Lit (LitBool b)) e1 e2)
  | Seq_C_Red e1 e2 : Reducible e1 → Reducible (Seq e1 e2)
  | Seq_D_Red e2 : Reducible (Seq (Lit LitUnit) e2)
  | Pair_L_Red e1 e2 : Reducible e1 → Reducible (Pair e1 e2)
  | Pair_R_Red e1 v1 e2 : to_val e1 = Some v1 → Reducible e2 → Reducible (Pair e1 e2)
  | Fst_C_Red e1 : Reducible e1 → Reducible (Fst e1)
  | Fst_D_Red e1 e2 v1 v2 : to_val e1 = Some v1 → to_val e2 = Some v2 → Reducible (Fst (Pair e1 e2))
  | Snd_C_Red e1 : Reducible e1 → Reducible (Snd e1)
  | Snd_D_Red e1 e2 v1 v2 : to_val e1 = Some v1 → to_val e2 = Some v2 → Reducible (Snd (Pair e1 e2))
  | InjL_Red e : Reducible e → Reducible (InjL e)
  | InjR_Red e : Reducible e → Reducible (InjR e)
  | Case_C_Red e e1 e2 : Reducible e → Reducible (Case e e1 e2)
  | Case_D_InjL_Red e v e1 e2 : to_val e = Some v → Reducible (Case (InjL e) e1 e2)
  | Case_D_InjR_Red e v e1 e2 : to_val e = Some v → Reducible (Case (InjR e) e1 e2)
  | Fold_Red e : Reducible e → Reducible (Fold e)
  | Unfold_C_Red e : Reducible e → Reducible (Unfold e)
  | Unfold_D_Red e v : to_val e = Some v → Reducible (Unfold (Fold e)).

Lemma Reducible_valid (e : expr) : reducible e tt <-> Reducible e.
Proof.
  induction e.
  Ltac local_tactic := (repeat lazymatch goal with
                               | |- reducible _ () => apply STLCmu_prim_red
                               | H : reducible _ () |- _ => destruct (iffRL (STLCmu_prim_red _) H) as [e' Hstep]
                               end).
  - split; intro red.
    + exfalso.
      assert (head_reducible (Var x) ()). apply prim_head_reducible; auto.
      apply (@ectxi_language_sub_redexes_are_values STLCmu_ectxi_lang).
      { intros Ki' e'' eqqq; destruct Ki'; inversion eqqq. }
      pose proof (iffRL (STLCmu_prim_head_red (Var x)) H).
      inversion H0. inversion H1.
    + exfalso. inversion red.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3. eapply LetIn_D_Red. eauto.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        simpl in *. apply LetIn_L_Red. apply IHe. inversion H1.
        apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      * pose proof (iffRL IHe H0). local_tactic.
        exists (LetIn e' e2). eapply (STLCmu_step_ctx (fill [LetInCtx _])); eauto.
      * exists e2.[e/]. apply head_prim_step. by econstructor.
  - split; intro red.
    + exfalso.
      assert (head_reducible (Lam e) ()). apply prim_head_reducible; auto.
      apply (@ectxi_language_sub_redexes_are_values STLCmu_ectxi_lang).
      { intros Ki' e'' eqqq; destruct Ki'; inversion eqqq. }
      pose proof (iffRL (STLCmu_prim_head_red (Lam e)) H).
      inversion H0. inversion H1.
    + exfalso. inversion red.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3. eapply App_D_Red. eauto.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        -- simpl in *. apply App_L_Red. apply IHe1. inversion H1.
           apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
        -- simpl in *. inversion H1. subst. eapply App_R_Red. by rewrite to_of_val.
           apply IHe2. apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      * pose proof (iffRL IHe1 H0). local_tactic.
        exists (App e' e2). eapply (STLCmu_step_ctx (fill [AppLCtx _])); eauto.
      * pose proof (iffRL IHe2 H2). local_tactic.
        exists (App e1 e'). rewrite -(of_to_val _ _ H1). eapply (STLCmu_step_ctx (fill [AppRCtx _])); eauto.
      * exists e0.[e2/]. apply head_prim_step. by econstructor.
  - split; intro red.
    + exfalso.
      assert (head_reducible (Lit l) ()). apply prim_head_reducible; auto.
      apply (@ectxi_language_sub_redexes_are_values STLCmu_ectxi_lang).
      { intros Ki' e'' eqqq; destruct Ki'; inversion eqqq. }
      pose proof (iffRL (STLCmu_prim_head_red (Lit l)) H).
      inversion H0. inversion H1.
    + exfalso. inversion red.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3. subst. rewrite -(of_to_val _ _ H5) -(of_to_val _ _ H7). eapply BinOp_D_Red.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        -- simpl in *. apply BinOp_L_Red. apply IHe1. inversion H1.
           apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
        -- simpl in *. inversion H1. subst. eapply BinOp_R_Red. by rewrite to_of_val.
           apply IHe2. apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      * pose proof (iffRL IHe1 H0). local_tactic.
        exists (BinOp op e' e2). eapply (STLCmu_step_ctx (fill [BinOpLCtx _ _])); eauto.
      * pose proof (iffRL IHe2 H3). local_tactic.
        exists (BinOp op e1 e'). rewrite -(of_to_val _ _ H1). eapply (STLCmu_step_ctx (fill [BinOpRCtx _ _])); eauto.
      * eexists _. apply head_prim_step. by econstructor.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3; subst; eapply If_D_Red.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        simpl in *. apply If_C_Red. apply IHe1. inversion H1.
        apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      * pose proof (iffRL IHe1 H0). local_tactic.
        exists (If e' e2 e3). eapply (STLCmu_step_ctx (fill [IfCtx _ _])); eauto.
      * destruct b; [exists e2 | exists e3]; apply head_prim_step; by econstructor.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3; subst. rewrite -(of_to_val _ _ H4). eapply Seq_D_Red.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        simpl in *. apply Seq_C_Red. apply IHe1. inversion H1.
        apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      * pose proof (iffRL IHe1 H0). local_tactic.
        exists (Seq e' e2). eapply (STLCmu_step_ctx (fill [SeqCtx _])); eauto.
      * exists e2; apply head_prim_step; by econstructor.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        -- simpl in *. apply Pair_L_Red. apply IHe1. inversion H1.
           apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
        -- simpl in *. inversion H1. subst. eapply Pair_R_Red. by rewrite to_of_val.
           apply IHe2. apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      * pose proof (iffRL IHe1 H0). local_tactic.
        exists (Pair e' e2). eapply (STLCmu_step_ctx (fill [PairLCtx _])); eauto.
      * pose proof (iffRL IHe2 H2). local_tactic.
        exists (Pair e1 e'). rewrite -(of_to_val _ _ H1). eapply (STLCmu_step_ctx (fill [PairRCtx _])); eauto.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3; subst. rewrite -(of_to_val _ _ H1) -(of_to_val _ _ H2). eapply Fst_D_Red; by rewrite to_of_val.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        simpl in *. apply Fst_C_Red. apply IHe. inversion H1.
        apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      * pose proof (iffRL IHe H0). local_tactic.
        exists (Fst e'). eapply (STLCmu_step_ctx (fill [FstCtx])); eauto.
      * exists e1; apply head_prim_step. econstructor. by rewrite H0. by rewrite H1.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3; subst. rewrite -(of_to_val _ _ H1) -(of_to_val _ _ H2). eapply Snd_D_Red; by rewrite to_of_val.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        simpl in *. apply Snd_C_Red. apply IHe. inversion H1.
        apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      * pose proof (iffRL IHe H0). local_tactic.
        exists (Snd e'). eapply (STLCmu_step_ctx (fill [SndCtx])); eauto.
      * exists e2; apply head_prim_step. econstructor. by rewrite H0. by rewrite H1.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3; subst.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        simpl in *. apply InjL_Red. apply IHe. inversion H1.
        apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      pose proof (iffRL IHe H0). local_tactic.
      exists (InjL e'). eapply (STLCmu_step_ctx (fill [InjLCtx])); eauto.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3; subst.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        simpl in *. apply InjR_Red. apply IHe. inversion H1.
        apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      pose proof (iffRL IHe H0). local_tactic.
      exists (InjR e'). eapply (STLCmu_step_ctx (fill [InjRCtx])); eauto.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3; subst.
        -- rewrite -(of_to_val _ _ H6). eapply Case_D_InjL_Red. by rewrite to_of_val.
        -- rewrite -(of_to_val _ _ H6). eapply Case_D_InjR_Red. by rewrite to_of_val.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        simpl in *. apply Case_C_Red. apply IHe. inversion H1.
        apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      * pose proof (iffRL IHe H0). local_tactic.
        exists (Case e' e1 e2). eapply (STLCmu_step_ctx (fill [CaseCtx _ _])); eauto.
      * exists e1.[e0/]. apply head_prim_step; by econstructor.
      * exists e2.[e0/]. apply head_prim_step; by econstructor.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3; subst.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        simpl in *. apply Fold_Red. apply IHe. inversion H1.
        apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      pose proof (iffRL IHe H0). local_tactic.
      exists (Fold e'). eapply (STLCmu_step_ctx (fill [FoldCtx])); eauto.
  - split; intro red.
    + pose proof (iffRL (STLCmu_prim_red _) red).
      inversion H. inversion_clear H0. simpl in *. subst. destruct K as [|Ki K _] using rev_ind.
      * simpl in *. subst. inversion H3; subst. rewrite -(of_to_val _ _ H1). eapply Unfold_D_Red; by rewrite to_of_val.
      * simpl in *. rewrite fill_app in H1. destruct Ki; try by inversion H1.
        simpl in *. apply Unfold_C_Red. apply IHe. inversion H1.
        apply STLCmu_prim_red. exists (fill K e2'). econstructor; eauto.
    + inversion red; subst; local_tactic.
      * pose proof (iffRL IHe H0). local_tactic.
        exists (Unfold e'). eapply (STLCmu_step_ctx (fill [UnfoldCtx])); eauto.
      * exists e0; apply head_prim_step. econstructor. by rewrite H0.
Qed.
