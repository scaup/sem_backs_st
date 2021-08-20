From st.STLCmuVS Require Import lang tactics lib.fixSTLCmuVS.
From iris.base_logic.lib Require Export ghost_map.
From iris.proofmode Require Import tactics.
Require Export st.backtranslations.st_sem.list_gmap.

Section ghost.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG STLCmuVS_lang Σ}.
  Context `{ghost_mapG_inst : !ghost_mapG Σ nat V}.

  Definition auth_list (γ : gname) (vs : list V) : iProp Σ :=
    ghost_map_auth γ 1 (list_gmap vs).

  Definition frag_elem (γ : gname) (i : nat) (v : V) : iProp Σ :=
    i ↪[ γ ] v. (* ghost_map_elem γ i (DfracOwn 1) v. *)

  Lemma ghost_empty :
    ⊢ |==> ∃ γ, auth_list γ [].
  Proof. by iApply ghost_map_alloc_empty. Qed.

  Lemma ghost_alloc γ vs v :
    auth_list γ vs -∗ |==> auth_list γ (vs ++ [v]) ∗ length vs ↪[ γ ] v.
  Proof.
    iIntros "Hvs".
    rewrite !/auth_list list_gmap_snoc.
    iApply (ghost_map_insert with "Hvs").
    rewrite -list_gmap_lookup. by apply lookup_ge_None.
  Qed.

  Lemma ghost_alloc_persist γ vs v :
    auth_list γ vs -∗ |==> auth_list γ (vs ++ [v]) ∗ length vs ↪[ γ ]□ v.
  Proof.
    iIntros "Hvs".
    rewrite !/auth_list list_gmap_snoc.
    iApply (ghost_map_insert_persist with "Hvs").
    rewrite -list_gmap_lookup. by apply lookup_ge_None.
  Qed.

  Lemma ghost_read γ vs i v :
    ⊢ auth_list γ vs -∗ i ↪[ γ ] v -∗ ⌜ vs !! i = Some v ⌝.
  Proof.
    iIntros "Hvs Hiv".
    rewrite /auth_list list_gmap_lookup.
    iApply (ghost_map_lookup with "Hvs Hiv").
  Qed.

  Lemma ghost_write γ vs v i v' :
    ⊢ auth_list γ vs -∗ i ↪[ γ ] v -∗ |==> auth_list γ (<[ i := v' ]> vs) ∗ i ↪[ γ ] v'.
  Proof.
    iIntros "Hvs Hiv".
    iDestruct (ghost_read with "Hvs Hiv") as %eq.
    rewrite !/auth_list (list_gmap_insert _ _ _ _ eq).
    iApply (ghost_map_update with "Hvs Hiv").
  Qed.

End ghost.

