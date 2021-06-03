From iris.program_logic Require Import lifting ectx_lifting.
From st.lamst Require Import lang.

Definition fresh_loc (σ : gmap loc val) : loc :=
  fresh (dom (gset loc) σ).

Lemma fresh_loc_lookup_None (σ : gmap loc lamst.lang.val) :
  σ !! fresh_loc σ = None.
Proof.
  rewrite /fresh_loc.
  by apply (not_elem_of_dom (D := gset loc)), is_fresh.
Qed.

Lemma inv_prim_step_Compare_locs (l1 l2 : loc) e2 (σ1 σ2 : state) κ efs (Hstep : prim_step (Compare l1 l2) σ1 κ e2 σ2 efs) :
  κ = [] ∧ efs = [] ∧ e2 = (bool_decide (l1 = l2)) ∧ σ1 = σ2.
Proof.
  simpl in *.
  assert (efs = []) as ->. by eapply ST_step_no_spawn.
  assert (κ = []) as ->. by eapply ST_step_no_obs.
  assert (Hheadstep : head_step (Compare l1 l2) σ1 [] e2 σ2 []). apply (@head_reducible_prim_step lamst_ectx_lang); auto.
  { exists [], (of_val $ bool_decide (l1 = l2)), σ1, []. simpl.
    destruct (decide (l1 = l2)) as [<- | neq].
    + rewrite bool_decide_eq_true_2; auto.
      apply Compare_suc_head_step.
    + rewrite bool_decide_eq_false_2; auto.
      by apply Compare_fail_head_step.
  }
  inversion_clear Hheadstep; auto;
    [by rewrite bool_decide_eq_true_2 | by rewrite bool_decide_eq_false_2].
Qed.

Lemma pure_step_eq_loc (l1 l2 : loc) : pure_step (Compare l1 l2)%Eₛₜ (of_val $ bool_decide (l1 = l2)).
Proof.
  split.
  - intros σ. rewrite /reducible_no_obs.
    exists (of_val $ bool_decide (l1 = l2)), σ, [].
    destruct (decide (l1 = l2)) as [<- | neq].
    + rewrite bool_decide_eq_true_2; auto. apply head_prim_step.
      (* Unset Printing Notations. Set Printing Coercions. *)
      apply Compare_suc_head_step.
    + rewrite bool_decide_eq_false_2; auto. apply head_prim_step.
      by apply Compare_fail_head_step.
  - intros. simpl in H.
    by destruct (inv_prim_step_Compare_locs _ _ _ _ _ _ _ H) as (-> & -> & -> & ->).
Qed.

