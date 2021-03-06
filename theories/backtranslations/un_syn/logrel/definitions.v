From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.STLCmuVS Require Import lang wkpre generic.lift contexts scopedness.
From st.STLCmu Require Import types.
From st.backtranslations.un_syn Require Import expressions universe.base.

Inductive refinement :=
  | syn_le_un (* syntactically-typed in universe ≤ untyped *)
  | un_le_syn. (* untyped ≤ syntactically-typed in universe *)

Existing Class refinement.

Section definitions.

  Context `{Σ : !gFunctors}.
  Context `{irisGS_inst : !irisGS STLCmuVS_lang Σ}.

  Context {rfn : refinement}.

  Definition s : stuckness := MaybeStuck.
    (* match rfn with *)
    (* | syn_le_un => NotStuck *)
    (* | un_le_syn => MaybeStuck (* untyped can of course get stuck *) *)
    (* end. *)

  Definition canon_tc_lift (tc : type_constructor) (Ψ : valO -n> valO -n> iPropO Σ) (xᵢ xₛ : valO) : iPropO Σ :=
    (match tc with
     | TCUnit => ⌜ xᵢ = ()%Vₙₒ ⌝ ∧ ⌜ xₛ = ()%Vₙₒ ⌝
     | TCBool => ∃ b : bool, ⌜ xᵢ = b%Vₙₒ ⌝ ∧ ⌜ xₛ = b ⌝
     | TCInt => ∃ z : Z, ⌜ xᵢ = z%Vₙₒ ⌝ ∧ ⌜ xₛ = z ⌝
     | TCProd => ∃ v1 v2 v1' v2', ⌜ xᵢ = (v1, v2)%Vₙₒ ⌝ ∧ ⌜ xₛ = (v1', v2')%Vₙₒ ⌝ ∧ (▷ Ψ v1 v1') ∗ (▷ Ψ v2 v2')
     | TCSum => ∃ vi vi', (⌜ xᵢ = InjLV vi ⌝ ∧ ⌜ xₛ = InjLV vi' ⌝ ∧ ▷ Ψ vi vi') ∨
                         (⌜ xᵢ = InjRV vi ⌝ ∧ ⌜ xₛ = InjRV vi' ⌝ ∧ ▷ Ψ vi vi')
     | TCArrow => ∃ e , ⌜ xᵢ = LamV e ⌝ ∧ ▷ □ (∀ w w', Ψ w w' -∗ lift s Ψ e.[of_val w/] (of_val xₛ w'))
     | TCRec => ∃ w w', ⌜ xᵢ = FoldV w ⌝ ∧ ⌜ xₛ = FoldV w' ⌝ ∧ ▷ Ψ w w'
     end)%I.

  Definition valrel_gen_pre (Ψ : valO -n> valO -n> iPropO Σ) (vᵢ vₛ : valO) : iPropO Σ :=
    match rfn with
    | syn_le_un => (∃ tc vᵢ', ⌜ vᵢ = inject_val tc vᵢ' ⌝ ∧ canon_tc_lift tc Ψ vᵢ' vₛ)%I
    | un_le_syn => (∃ tc vₛ', ⌜ vₛ = inject_val tc vₛ' ⌝ ∧ canon_tc_lift tc Ψ vᵢ vₛ')%I
    end.

  Definition valrel_gen (Ψ : valO -n> valO -n> iPropO Σ) : valO -n> valO -n> iPropO Σ := λne v v', valrel_gen_pre Ψ v v'.

  Instance valrel_gen_contractive : Contractive valrel_gen.
  Proof.
    intros n P1 P2 dl. rewrite /valrel_gen. intros v v'. simpl.
    rewrite /valrel_gen_pre; destruct rfn; f_equiv; intro tc; rewrite /inject_val /InjVTC /canon_tc_lift; destruct tc; rewrite /lift; solve_contractive.
  Qed.

  Definition valrel := fixpoint valrel_gen.

  Lemma valrel_unfold v1 v2 : fixpoint valrel_gen v1 v2 ≡ valrel_gen (fixpoint valrel_gen) v1 v2.
  Proof. do 2 f_equiv. by rewrite -fixpoint_unfold. Qed.

  Global Instance valrel_persistent u v' : Persistent (valrel u v').
  Proof.
    rewrite /Persistent. revert u v'. iLöb as "IHlob". iIntros (u v') "Huv'".
    rewrite valrel_unfold /= /valrel_gen_pre. destruct rfn.
    { iDestruct "Huv'" as (tc v) "[-> Hvv']".
    iExists tc, v. iSplit; auto. destruct tc; try by iDestruct "Hvv'" as "#Hvv'".
    - simpl; fold valrel. iDestruct "Hvv'" as (v1 v2 v1' v2') "(-> & -> & H1 & H2)".
      iExists v1, v2, v1', v2'. repeat iSplit; auto.
      iApply bi.later_persistently_1. iNext. by iApply "IHlob".
      iApply bi.later_persistently_1. iNext. by iApply "IHlob".
    - simpl; fold valrel. iDestruct "Hvv'" as (vi vi') "[(-> & -> & H) | (-> & -> & H)]".
      iExists _, _. iLeft. repeat iSplit; auto. iApply bi.later_persistently_1. by iApply "IHlob".
      iExists _, _. iRight. repeat iSplit; auto. iApply bi.later_persistently_1. by iApply "IHlob".
    - simpl. fold valrel. iDestruct "Hvv'" as (w w') "(-> & -> & H)".
      iExists _,_. repeat iSplit; auto. iApply bi.later_persistently_1. by iApply "IHlob". }
    { iDestruct "Huv'" as (tc v) "[-> Hvv']".
    iExists tc, v. iSplit; auto. destruct tc; try by iDestruct "Hvv'" as "#Hvv'".
    - simpl; fold valrel. iDestruct "Hvv'" as (v1 v2 v1' v2') "(-> & -> & H1 & H2)".
      iExists v1, v2, v1', v2'. repeat iSplit; auto.
      iApply bi.later_persistently_1. iNext. by iApply "IHlob".
      iApply bi.later_persistently_1. iNext. by iApply "IHlob".
    - simpl; fold valrel. iDestruct "Hvv'" as (vi vi') "[(-> & -> & H) | (-> & -> & H)]".
      iExists _, _. iLeft. repeat iSplit; auto. iApply bi.later_persistently_1. by iApply "IHlob".
      iExists _, _. iRight. repeat iSplit; auto. iApply bi.later_persistently_1. by iApply "IHlob".
    - simpl. fold valrel. iDestruct "Hvv'" as (w w') "(-> & -> & H)".
      iExists _,_. repeat iSplit; auto. iApply bi.later_persistently_1. by iApply "IHlob". }
  Qed.

  Definition exprel : exprO -n> exprO -n> iPropO Σ :=
    λne eᵢ eₛ, lift s valrel eᵢ eₛ.

  Definition open_exprel (n : nat) (e : expr) (e' : expr) : Prop :=
    ∀ (us : list val) (vs' : list val), length us = n →
      ([∗ list] uᵢ ; vᵢ' ∈ us ; vs', valrel uᵢ vᵢ') ⊢
        exprel e.[subst_list_val us] e'.[subst_list_val vs'].

  Lemma open_exprel_nil e e' : (⊢ exprel e e') -> open_exprel 0 e e'.
  Proof. iIntros (Hee' vs vs' Hl) "Hvv'". destruct vs, vs'; try by inversion Hl. asimpl. iApply Hee'. Qed.

  Lemma open_exprel_nil' e e' : open_exprel 0 e e' → (⊢ exprel e e').
  Proof. iIntros (Hee'). iDestruct (Hee' [] []) as "H". auto. asimpl. by iApply "H". Qed.

  Definition ctx_rel (n m : nat)
             (C : ctx)
             (C' : ctx) :=
    ∀ e e' , open_exprel n e e' → open_exprel m (fill_ctx C e) (fill_ctx C' e').

  Lemma ctx_rel_app (n m l : nat) (C1 C1' C2 C2' : ctx) :
    ctx_rel n m C2 C2' → ctx_rel m l C1 C1' →
    ctx_rel n l (C1 ++ C2) (C1' ++ C2').
  Proof. intros H2 H1 e e' Hee'. rewrite -!fill_ctx_app. apply H1, H2, Hee'. Qed.

End definitions.
