From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst.
From st.lam Require Import types lang typing tactics logrel.definitions logrel.generic.lift.
From st.lam.lib Require Import fixlam universe.embed_project guard_assert universe.base.
From st.backtranslations.un_syn Require Import logrel.definitions.
(* logrel.un_le_syn.fundamental. *)

(* Defines connective lemma between the untyped and typed logic relations (the (syntactically typed ≤ untyped)-refinement) *)
(* Of the two refinements, this is the easier one *)
Section connective_syn_le_un.

  Instance rfn' : refinement := syn_le_un.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.


  Print Instances refinement.

End connective_syn_le_un.
