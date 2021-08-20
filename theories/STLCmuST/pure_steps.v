From iris.program_logic Require Import language ectx_language ectxi_language.
From st.prelude Require Export autosubst generic.
From stdpp Require Import gmap prelude.
From st.STLCmuST Require Import lang.

Definition state_stuff (e : expr) : bool :=
  match e with
  | Return e => true
  | Bind e1 e2 => true
  | RunST e => true
  | Alloc e => true
  | Read e => true
  | Write e1 e2 => true
  | Compare e1 e2 => true
  | _ => false
  end.

Lemma head_step_pure_step e e' :
  (state_stuff e = false) →
  head_step e ∅ [] e' ∅ [] → pure_step e e'.
Proof.
  Ltac blaaa :=
    apply pure_head_step_pure_step; split;
    [ intros; eexists _, _, _; econstructor; eauto
    | intros σ1 κ e2' σ2 efs Hstep;
      match goal with
      | H : ectx_language.head_step _ _ _ _ _ _ |- _ => inversion H
      end; auto
    ].
  intros b Hs. inversion Hs; (try by (subst; inversion b)); blaaa; try done.
  rewrite H in H12. rewrite H0 in H13. inversion H12. inversion H13. auto.
Qed.
