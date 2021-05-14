From iris Require Import program_logic.weakestpre.
From st.lamst Require Import lang types typing.
From st.lam Require Import lang wkpre generic.lift.
From st.backtranslations.st_sem Require Import ghost heap expressions.
From st.backtranslations.st_sem.well_defined.logrel Require Import definition.
From iris.proofmode Require Import tactics.
Require Import compat_lemmas.

Section fundamental_theorem.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.
  Context `{ghost_mapG_inst : !ghost_mapG Σ nat (prod val val)}.

  Set Nested Proofs Allowed.

  Lemma fundamental (Γ : list lamst.types.type) (e : lamst.lang.expr) (τ : lamst.types.type)
        (d : Γ ⊢ₛₜ e : τ) :
    open_exprel_typed Γ <<e>> <<e>> τ.
  Proof.
    induction d; simpl.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
      (* !! intersting ones !! *)

    - (* alloc *)
      (* cleaning and getting to the gist of it *)
      iIntros (Δ vs vs') "#Hvsvs'".
      specialize (IHd Δ vs vs').
      iDestruct (IHd with "Hvsvs'") as "Hee'". clear IHd. iClear "Hvsvs'".
      admit.
    - (* read *)
      (* cleaning and getting to the gist of it *)
      iIntros (Δ vs vs') "#Hvsvs'".
      specialize (IHd Δ vs vs').
      iDestruct (IHd with "Hvsvs'") as "Hee'". clear IHd. iClear "Hvsvs'".
      admit.
    - (* write *)
      (* cleaning and getting to the gist of it *)
      iIntros (Δ vs vs') "#Hvsvs'".
      specialize (IHd1 Δ vs vs').
      iDestruct (IHd1 with "Hvsvs'") as "Hee'". clear IHd1.
      specialize (IHd2 Δ vs vs'). clear IHd2.
      iClear "Hvsvs'".
      admit.
    - (* bind *)
      admit.
    - (* return *)
      admit.
    - (* runst *)
      admit.
    - (* equal *)
      admit.

