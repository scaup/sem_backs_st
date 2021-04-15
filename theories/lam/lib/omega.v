From st.lam Require Import types lang typing tactics.

Definition Ω : expr :=
  (Lam (Unfold %0 %0)
       (Fold (Lam (Unfold %0 %0)))
  )%Eₙₒ.
  (* (Fix (Lam %0))%Eₙₒ. *)
  (* (Rec (%0 %1) ())%Eₙₒ. *)

Lemma Ω_Closed : Closed Ω.
Proof. intro σ. by asimpl. Qed.

Lemma Ω_typed Γ τ : Γ ⊢ₙₒ Ω : τ.
Proof.
  apply App_typed with (τ1 := TRec (TVar 0 ⟶ τ.[ren (+1)])%Tₙₒ).
  apply Lam_typed. apply App_typed with (τ1 := TRec (TVar 0 ⟶ τ.[ren (+1)])%Tₙₒ). assert ((TRec (TVar 0 ⟶ τ.[ren (+1)]) ⟶ τ)%Tₙₒ = (TVar 0 ⟶ τ.[ren (+1)])%Tₙₒ.[TRec (TVar 0 ⟶ τ.[ren (+1)])%Tₙₒ/]) as ->. by asimpl. do 3 econstructor.
  by econstructor. econstructor. asimpl.
  apply Lam_typed. apply App_typed with (τ1 := TRec (TVar 0 ⟶ τ.[ren (+1)])%Tₙₒ). assert ((TRec (TVar 0 ⟶ τ.[ren (+1)]) ⟶ τ)%Tₙₒ = (TVar 0 ⟶ τ.[ren (+1)])%Tₙₒ.[TRec (TVar 0 ⟶ τ.[ren (+1)])%Tₙₒ/]) as ->. by asimpl. do 3 econstructor.
  by econstructor.
Qed.

Lemma Ω_loop : nsteps lam_step 2 Ω Ω.
Proof. do 2 (eapply nsteps_l; first auto_lam_step; simpl). by apply nsteps_O. Qed.

(* From st.lam Require Import wkpre. *)
(* From iris Require Import program_logic.weakestpre. *)
(* From iris.proofmode Require Import tactics. *)

(* Lemma wp_Ω Φ : ⊢ WP Ω {{Φ}}. *)
(* Proof. iLöb as "IH". iApply wp_steps_later. by apply Ω_loop. done. Qed. *)

Global Opaque Ω.
