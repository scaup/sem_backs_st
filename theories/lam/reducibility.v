From iris.program_logic Require Import language ectxi_language ectx_language lifting.
From st.lam Require Import tactics lang.

Definition lam_head_step (e e' : expr) := head_step e tt [] e' tt [].

Lemma head_to_lam_head (e e' : expr) σ σ' κ efs : head_step e σ κ e' σ' efs → lam_head_step e e'.
Proof. intro H. rewrite /lam_head_step. inversion H; by econstructor. Qed.

Definition lam_reducible (e : expr) := ∃ e', lam_step e e'.
Definition lam_irreducible (e : expr) := ∀ e', ¬ lam_step e e'.
Definition lam_head_reducible (e : expr) := ∃ e', lam_head_step e e'.
Definition lam_head_irreducible (e : expr) := ∀ e', ¬ lam_head_step e e'.

Lemma prim_to_lam (e1 e2 : expr) σ1 σ2 κ efs : prim_step e1 σ1 κ e2 σ2 efs -> lam_step e1 e2.
Proof. intro H. apply lam_pure. apply (prim_step_pure _ _ _ _ _ _ H). Qed.

Lemma lam_prim_red (e : expr) : lam_reducible e <-> reducible e tt.
Proof.
  split. intro H. destruct H as [e' Hstep]. exists [], e', tt, []. apply Hstep.
  intro H. destruct H as (a & e' & b & c & Hstep). exists e'. by eapply prim_to_lam.
Qed.
Lemma lam_prim_irred (e : expr) : lam_irreducible e <-> irreducible e tt.
Proof.
  split.
  + rewrite /lam_irreducible /irreducible.
    intros. intro abs. apply (H e'). by eapply prim_to_lam.
  + intros H e' abs. rewrite /irreducible in H. by apply (H [] e' () []).
Qed.
Lemma lam_prim_head_red (e : expr) : lam_head_reducible e <-> head_reducible e tt.
Proof.
  split. intro H. destruct H as [e' Hstep]. exists [], e', tt, []. apply Hstep.
  intro H. destruct H as (a & e' & b & c & Hstep). exists e'. destruct Hstep; by econstructor.
Qed.
Lemma lam_prim_head_irred (e : expr) : lam_head_irreducible e <-> head_irreducible e tt.
Proof.
  split. intro H. intros κ e' σ efs abs. apply (H e'). by eapply head_to_lam_head.
  intros H e' Hstep. apply (H [] e' () []). auto.
Qed.

Lemma stuck_no_val_irred e : (to_val e = None) → stuck e tt → irreducible e tt.
Proof. rewrite /stuck. intuition. Qed.

Ltac head_stuck_solver :=
  lazymatch goal with
  | |- stuck ?e () => apply head_stuck_stuck; head_stuck_solver
  | |- head_stuck ?e () => split; head_stuck_solver
  | |- rtc lam_step _ _ => (eapply rtc_l; first (auto_lam_step); simplify_custom)
  | |- ectx_language.to_val _ = _ => (by simplify_custom) ; head_stuck_solver
  | |- head_irreducible _ () => ((apply lam_prim_head_irred; intros e' abs; inversion abs; simplify_option_eq); try done); head_stuck_solver
  | |- sub_redexes_are_values _ => apply ectxi_language_sub_redexes_are_values; intros Ki' e' eqqq; destruct Ki'; inversion eqqq; head_stuck_solver
  | |- is_Some _ => (by eexists; simplify_custom) ; head_stuck_solver
  | |- _ => auto
  end.

Inductive reducibility (e : expr) : Type :=
  | is_val v : to_val e = Some v → reducibility e
  | is_red : reducible e tt → reducibility e
  | is_stuck : stuck e tt → reducibility e.

Lemma fill_stuck (K : list ectx_item) (e : expr) :
    stuck e tt → stuck (fill K e) tt.
Proof. apply stuck_fill. Qed.

Lemma dec_expr_reducibility (e : expr) : reducibility e.
Proof.
  induction e as [x | e1 IH1 e2 IH2 | e _ | e1 IH1 e2 IH2 | | op e1 IH1 e2 IH2 | e0 IH0 e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH | e IH | e IH | e IH | e0 IH0 e1 IH1 e2 IH2 | e IH | e IH | e IH ];
    (try by eapply is_val).
  - apply is_stuck. head_stuck_solver.
  - destruct IH1 as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + apply is_red; apply lam_prim_red; eexists; auto_lam_step.
    + apply is_red; by apply (fill_reducible [LetInCtx _]).
    + apply is_stuck; by apply (fill_stuck [LetInCtx _]).
  - destruct IH1 as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + destruct IH2 as [ v2 eq2 | is_red2 | is_stuck2 ]; [ rewrite -(of_to_val _ _ eq2) | | ].
      * destruct v1; try by (apply is_stuck; head_stuck_solver).
        apply is_red; apply lam_prim_red; eexists; auto_lam_step.
      * apply is_red; by apply (fill_reducible [AppRCtx _]).
      * apply is_stuck; by apply (fill_stuck [AppRCtx _]).
    + apply is_red; by apply (fill_reducible [AppLCtx _]).
    + apply is_stuck; by apply (fill_stuck [AppLCtx _]).
  - destruct IH1 as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + destruct IH2 as [ v2 eq2 | is_red2 | is_stuck2 ]; [ rewrite -(of_to_val _ _ eq2) | | ].
      * destruct v1; (lazymatch goal with | v : base_lit |- _ => destruct v | |- _ => auto end); try by (apply is_stuck; head_stuck_solver).
        destruct v2; (lazymatch goal with | v : base_lit |- _ => destruct v | |- _ => auto end); try by (apply is_stuck; head_stuck_solver).
        apply is_red; apply lam_prim_red; eexists; auto_lam_step.
      * apply is_red; by apply (fill_reducible [BinOpRCtx _ _]).
      * apply is_stuck; by apply (fill_stuck [BinOpRCtx _ _]).
    + apply is_red; by apply (fill_reducible [BinOpLCtx _ _]).
    + apply is_stuck; by apply (fill_stuck [BinOpLCtx _ _]).
  - destruct IH0 as [ v0 eq0 | is_red0 | is_stuck0 ]; [ rewrite -(of_to_val _ _ eq0) | | ].
    + destruct v0; (lazymatch goal with | v : base_lit |- _ => destruct v | |- _ => auto end); try by (apply is_stuck; head_stuck_solver).
      destruct b; apply is_red; apply lam_prim_red; eexists; auto_lam_step.
    + apply is_red; by apply (fill_reducible [IfCtx _ _]).
    + apply is_stuck; by apply (fill_stuck [IfCtx _ _]).
  - destruct IH1 as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + destruct v1; (lazymatch goal with | v : base_lit |- _ => destruct v | |- _ => auto end); try by (apply is_stuck; head_stuck_solver).
      apply is_red; apply lam_prim_red; eexists; auto_lam_step.
    + apply is_red; by apply (fill_reducible [SeqCtx _]).
    + apply is_stuck; by apply (fill_stuck [SeqCtx _]).
  - destruct IH1 as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + destruct IH2 as [ v2 eq2 | is_red2 | is_stuck2 ]; [ rewrite -(of_to_val _ _ eq2) | | ].
      * by apply (is_val _ (v1, v2)%Vₙₒ); simplify_custom.
      * apply is_red; by apply (fill_reducible [PairRCtx _]).
      * apply is_stuck; by apply (fill_stuck [PairRCtx _]).
    + apply is_red; by apply (fill_reducible [PairLCtx _]).
    + apply is_stuck; by apply (fill_stuck [PairLCtx _]).
  - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + destruct v1; try by (apply is_stuck; head_stuck_solver).
      apply is_red; apply lam_prim_red; eexists; auto_lam_step.
    + apply is_red. by apply (fill_reducible [FstCtx]).
    + apply is_stuck; by apply (fill_stuck [FstCtx]).
  - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + destruct v1; try by (apply is_stuck; head_stuck_solver).
      apply is_red; apply lam_prim_red; eexists; auto_lam_step.
    + apply is_red. by apply (fill_reducible [SndCtx]).
    + apply is_stuck; by apply (fill_stuck [SndCtx]).
  - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + apply (is_val _ (InjLV v1)). by simplify_custom.
    + apply is_red. by apply (fill_reducible [InjLCtx]).
    + apply is_stuck; by apply (fill_stuck [InjLCtx]).
  - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + apply (is_val _ (InjRV v1)). by simplify_custom.
    + apply is_red. by apply (fill_reducible [InjRCtx]).
    + apply is_stuck; by apply (fill_stuck [InjRCtx]).
  - destruct IH0 as [ v0 eq0 | is_red0 | is_stuck0 ]; [ rewrite -(of_to_val _ _ eq0) | | ].
    + (destruct v0; try by (apply is_stuck; head_stuck_solver));
      apply is_red; apply lam_prim_red; eexists; auto_lam_step.
    + apply is_red; by apply (fill_reducible [CaseCtx _ _]).
    + apply is_stuck; by apply (fill_stuck [CaseCtx _ _]).
  - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + apply (is_val _ (FoldV v1)). by simplify_custom.
    + apply is_red. by apply (fill_reducible [FoldCtx]).
    + apply is_stuck; by apply (fill_stuck [FoldCtx]).
  - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + destruct v1; try by (apply is_stuck; head_stuck_solver).
      apply is_red; apply lam_prim_red; eexists; auto_lam_step.
    + apply is_red. by apply (fill_reducible [UnfoldCtx]).
    + apply is_stuck; by apply (fill_stuck [UnfoldCtx]).
  - destruct IH as [ v1 eq1 | is_red1 | is_stuck1 ]; [ rewrite -(of_to_val _ _ eq1) | | ].
    + destruct v1; apply is_red; apply lam_prim_red; eexists; auto_lam_step.
    + apply is_red. by apply (fill_reducible [GhostStepCtx]).
    + apply is_stuck; by apply (fill_stuck [GhostStepCtx]).
Qed.

