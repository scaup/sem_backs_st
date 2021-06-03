From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.

Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

From st.prelude Require Import big_op_three.

From st.lamst Require Import lang types.
From st.lam Require Import lang wkpre .

From st.backtranslations.st_sem Require Import ghost heap_emul.base.
From st.backtranslations.st_sem.correctness.sem_le_st.logrel Require Import lift.

Section value_relation.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Context `{genHeapG_inst : !gen_heapG loc lamst.lang.val Σ}.

  Context `{val_ghost_mapG_inst : !ghost_mapG Σ nat val}.
  Context `{loc_ghost_mapG_inst : !ghost_mapG Σ nat loc}.

  (* Context `{inG_Σ_auth_nat_to_ag_loc : !inG Σ () } *)
  Context (Δ : list (gname * gname)).

  Fixpoint valrel_typed_gen_pre (Ψ : typeO -n> valO -n> lamst.lang.valO -n> iPropO Σ) (τ : typeO) : valO -n> lamst.lang.valO -n> iPropO Σ := λne v v',
    (match τ with
     | TUnit => ⌜ v = (()%Vₙₒ : valO) ⌝ ∧ ⌜ v' = (()%Vₛₜ : lamst.lang.valO) ⌝
     | TBool => ∃ b : bool, ⌜ v = b ⌝ ∧ ⌜ v' = b ⌝
     | TInt => ∃ z : Z, ⌜ v = z ⌝ ∧ ⌜ v' = z ⌝
     | TProd τ1 τ2 => ∃ v1 v2 v1' v2', ⌜ v = (v1, v2)%Vₙₒ ⌝ ∧ ⌜ v' = (v1' , v2')%Vₛₜ⌝ ∗ valrel_typed_gen_pre Ψ τ1 v1 v1' ∗ valrel_typed_gen_pre Ψ τ2 v2 v2'
     | TSum τ1 τ2 => ∃ vi vi', (⌜ v = InjLV vi ⌝ ∧ ⌜ v' = lamst.lang.InjLV vi' ⌝ ∧ valrel_typed_gen_pre Ψ τ1 vi vi') ∨
                              (⌜ v = InjRV vi ⌝ ∧ ⌜ v' = lamst.lang.InjRV vi' ⌝ ∧ valrel_typed_gen_pre Ψ τ2 vi vi')
     | TArrow τ1 τ2 => □ (∀ w w', valrel_typed_gen_pre Ψ τ1 w w' -∗ lift MaybeStuck (valrel_typed_gen_pre Ψ τ2) (v w) (v' w'))
     | TRec τb => ∃ w w', ⌜ v = FoldV w ⌝ ∧ ⌜ v' = lamst.lang.FoldV w' ⌝ ∧ ▷ (Ψ τb.[TRec τb/] w w')
     | TVar X => False
     | TSTref ρ τ =>
       match ρ with
       | TVar X =>
         match Δ !! X with
         | Some (γ, γ') => ∃ (i : nat) (l : loc), ⌜ v = i ⌝ ∗ ⌜ v' = l ⌝ ∗ i ↪[γ']□ l ∗
                             inv (nroot .@ γ .@ γ' .@ i) (∃ (w : val) (w' : lamst.lang.val), i ↪[γ] w ∗ l ↦ w' ∗ valrel_typed_gen_pre Ψ τ w w')
         | None => False
         end
       | _ => False
       end
     | TST ρ τ' =>
       match ρ with
       | TVar X =>
         match Δ !! X with
         | Some (γ, γ') => ∀ (psᵢ : list (val *loc)) (σ : gmap loc lamst.lang.val),
             let vsᵢ := psᵢ.*1 in
             let lsᵢ := psᵢ.*2 in
             □ (gen_heap_interp σ -∗ auth_list γ vsᵢ -∗ auth_list γ' lsᵢ -∗
                          WP v (encode vsᵢ) ?{{ r, ∃ (w : val) (w' : lamst.lang.val) (psₜ : list (val * loc)) (σ' : gmap loc lamst.lang.val),
                                                let vsₜ := psₜ.*1 in
                                                let lsₜ := psₜ.*2 in
                                                ⌜ r = (encode vsₜ, w)%Vₙₒ⌝ ∗
                                                gen_heap_interp σ' ∗
                                                auth_list γ vsₜ ∗
                                                auth_list γ' lsₜ ∗
                                                ⌜ rtc lamst_step (σ, RunST v') (σ', lamst.lang.of_val w') ⌝ ∧
                                                valrel_typed_gen_pre Ψ τ' w w'
                                           }}
               )
         | None => True
         end
       | _ => True
       end
     end)%I.

  Definition valrel_typed_gen (Ψ : typeO -n> valO -n> lamst.lang.valO -n> iPropO Σ) : typeO -n> valO -n> lamst.lang.valO -n> iPropO Σ := λne τ v v', valrel_typed_gen_pre Ψ τ v v'.

  Instance valrel_typed_gen_contractive : Contractive valrel_typed_gen.
  Proof.
    intros n P1 P2 dl. rewrite /valrel_typed_gen. intro τ. simpl.
    induction τ; try by solve_contractive.
    - intros v v'. simpl. do 6 f_equiv. specialize (IHτ1 a a0). simpl in IHτ1. by rewrite IHτ1.
      rewrite /lift. do 9 f_equiv. specialize (IHτ2 a2 a3). simpl in IHτ2. by rewrite IHτ2.
    - intros v v'. simpl. destruct τ1; try done. clear IHτ1.
      destruct (Δ !! X) as [[γ γ']|] eqn:eq; auto.
      repeat (f_equiv; try by solve_contractive).
  Qed.

  Definition valrel_typed := fixpoint valrel_typed_gen.

  Lemma valrel_typed_unfold τ v1 v2 : valrel_typed τ v1 v2 ≡ valrel_typed_gen (fixpoint valrel_typed_gen) τ v1 v2.
  Proof. do 3 f_equiv. by rewrite -fixpoint_unfold. Qed.
  Lemma valrel_typed_unfold' τ : valrel_typed τ ≡ valrel_typed_gen (fixpoint valrel_typed_gen) τ.
  Proof. intros x x'. by rewrite valrel_typed_unfold. Qed.
  Lemma valrel_typed_unfold'': valrel_typed ≡ valrel_typed_gen (fixpoint valrel_typed_gen).
  Proof. intros x. by rewrite valrel_typed_unfold'. Qed.
  Lemma valrel_typed_gen_pre_gen Ψ τ v v' : valrel_typed_gen_pre Ψ τ v v' ≡ valrel_typed_gen Ψ τ v v'.
  Proof. auto. Qed.
  Lemma valrel_typed_gen_pre_gen' Ψ τ : valrel_typed_gen_pre Ψ τ ≡ valrel_typed_gen Ψ τ.
  Proof. intro. intro. auto. Qed.

  Lemma valrel_typed_TUnit_unfold v v' : valrel_typed TUnit v v' ≡ (⌜ v = (()%Vₙₒ : valO) ⌝ ∧ ⌜ v' = (()%Vₛₜ : lamst.lang.valO) ⌝)%I.
  Proof. by rewrite valrel_typed_unfold. Qed.
  Lemma valrel_typed_TBool_unfold v v' : valrel_typed TBool v v' ≡ (∃ b : bool, ⌜ v = b ⌝ ∧ ⌜ v' = b ⌝)%I.
  Proof. by rewrite valrel_typed_unfold. Qed.
  Lemma valrel_typed_TInt_unfold v v' : valrel_typed TInt v v' ≡ (∃ z : Z, ⌜ v = z ⌝ ∧ ⌜ v' = z ⌝)%I.
  Proof. by rewrite valrel_typed_unfold. Qed.
  Lemma valrel_typed_TArrow_unfold τ1 τ2 v v' : valrel_typed (TArrow τ1 τ2) v v' ≡ (□ (∀ w w', valrel_typed τ1 w w' -∗ lift MaybeStuck (valrel_typed τ2) (v w) (v' w')))%I.
  Proof.
    rewrite valrel_typed_unfold. rewrite /valrel_typed_gen. simpl.
    f_equiv. f_equiv. intros w. f_equiv. intro w'. f_equiv.
    - rewrite valrel_typed_gen_pre_gen. unfold valrel_typed. rewrite -valrel_typed_unfold. auto.
    - rewrite /lift. f_equiv. simpl. repeat (f_equiv; try by rewrite valrel_typed_unfold).
  Qed.
  Lemma valrel_typed_TSum_unfold τ1 τ2 v v' : valrel_typed (TSum τ1 τ2) v v' ≡ (∃ vi vi', (⌜ v = InjLV vi ⌝ ∧ ⌜ v' = lamst.lang.InjLV vi' ⌝ ∧ valrel_typed τ1 vi vi') ∨ (⌜ v = InjRV vi ⌝ ∧ ⌜ v' = lamst.lang.InjRV vi' ⌝ ∧ valrel_typed τ2 vi vi'))%I.
  Proof. rewrite valrel_typed_unfold. simpl. repeat f_equiv; rewrite valrel_typed_gen_pre_gen'; rewrite -valrel_typed_unfold'; auto. Qed.
  Lemma valrel_typed_TProd_unfold τ1 τ2 v v' : valrel_typed (TProd τ1 τ2) v v' ≡ (∃ v1 v2 v1' v2', ⌜ v = (v1, v2)%Vₙₒ ⌝ ∧ ⌜ v' = (v1' , v2')%Vₛₜ ⌝ ∗ valrel_typed τ1 v1 v1' ∗ valrel_typed τ2 v2 v2')%I.
  Proof. rewrite valrel_typed_unfold. simpl. repeat f_equiv; rewrite valrel_typed_gen_pre_gen'; rewrite -valrel_typed_unfold'; auto. Qed.
  Lemma valrel_typed_TRec_unfold τ v v' : valrel_typed (TRec τ) v v' ≡ (∃ w w', ⌜ v = FoldV w ⌝ ∧ ⌜ v' = lamst.lang.FoldV w' ⌝ ∧ ▷ (valrel_typed τ.[TRec τ/] w w'))%I.
  Proof. rewrite valrel_typed_unfold. simpl. repeat f_equiv; rewrite valrel_typed_gen_pre_gen'; rewrite -valrel_typed_unfold'; auto. Qed.
  Lemma valrel_typed_TVar_unfold X v v' : valrel_typed (TVar X) v v' ≡ False%I.
  Proof. rewrite valrel_typed_unfold. by simpl. Qed.
  Lemma valrel_typed_TSTRef_unfold ρ τ v v' :
    valrel_typed (TSTref ρ τ) v v' ≡
                 (match ρ with
                  | TVar X =>
                    match Δ !! X with
                    | Some (γ, γ') => ∃ (i : nat) (l : loc), ⌜ v = i ⌝ ∗ ⌜ v' = l ⌝ ∗ i ↪[γ']□ l ∗
                                                          inv (nroot .@ γ .@ γ' .@ i) (∃ (w : val) (w' : lamst.lang.val), i ↪[γ] w ∗ l ↦ w' ∗ valrel_typed τ w w')
                 | None => False
                  end
                 | _ => False
                  end)%I.
  Proof. rewrite valrel_typed_unfold. simpl. repeat f_equiv. rewrite valrel_typed_gen_pre_gen'; rewrite -valrel_typed_unfold'; auto. Qed.
  Lemma valrel_typed_TST_unfold ρ τ v v' :
    valrel_typed (TST ρ τ) v v' ≡
      (match ρ with
       | TVar X =>
         match Δ !! X with
         | Some (γ, γ') => ∀ (psᵢ : list (val *loc)) (σ : gmap loc lamst.lang.val),
             let vsᵢ := psᵢ.*1 in
             let lsᵢ := psᵢ.*2 in
             □ (gen_heap_interp σ -∗ auth_list γ vsᵢ -∗ auth_list γ' lsᵢ -∗
                          WP v (encode vsᵢ) ?{{ r, ∃ (w : val) (w' : lamst.lang.val) (psₜ : list (val * loc)) (σ' : gmap loc lamst.lang.val),
                                                let vsₜ := psₜ.*1 in
                                                let lsₜ := psₜ.*2 in
                                                ⌜ r = (encode vsₜ, w)%Vₙₒ⌝ ∗
                                                gen_heap_interp σ' ∗
                                                auth_list γ vsₜ ∗
                                                auth_list γ' lsₜ ∗
                                                ⌜ rtc lamst_step (σ, RunST v') (σ', lamst.lang.of_val w') ⌝ ∧
                                                valrel_typed τ w w'
                                           }}
               )
         | None => True
         end
       | _ => True
       end
      )%I.
  Proof. rewrite valrel_typed_unfold. simpl. repeat f_equiv. rewrite valrel_typed_gen_pre_gen'; rewrite -valrel_typed_unfold'; auto. Qed.

  Global Instance valrel_typed_persistent τ v v' : Persistent (valrel_typed τ v v').
  Proof.
    rewrite /Persistent. revert τ v v'. iLöb as "IHlob". iIntros (τ).
    iInduction τ as [ | | | τ1 τ2 | τ1 τ2 | τ1 τ2 | τ1 τ2 | τb | ρ τ | ρ τ ] "IH";
      iIntros (v v'); try by rewrite valrel_typed_unfold; iIntros "#H".
    - rewrite valrel_typed_TProd_unfold. iIntros "H". iDestruct "H" as (v1 v2 v1' v2') "(-> & -> & H1 & H2)".
      iExists v1, v2, v1', v2'. repeat iSplit; auto. iApply ("IH" with "H1"). iApply ("IH1" with "H2").
    - rewrite valrel_typed_TSum_unfold. iIntros "H". iDestruct "H" as (vi vi') "[(-> & -> & H1) | (-> & -> & H2)]"; iExists vi, vi'.
      + iLeft. repeat iSplit; auto. by iApply ("IH" with "H1").
      + iRight. repeat iSplit; auto. by iApply ("IH1" with "H2").
    - rewrite valrel_typed_TRec_unfold. iIntros "H". iDestruct "H" as (w w') "(-> & -> & H)". iExists w, w'. repeat iSplitL ""; auto.
      iApply bi.later_persistently_1. iNext. by iApply "IHlob".
    - rewrite valrel_typed_TSTRef_unfold. destruct ρ; auto.
      destruct (Δ !! X); auto. destruct p; auto.
    - rewrite valrel_typed_TST_unfold. destruct ρ; auto.
      destruct (Δ !! X); auto. destruct p; auto.
  Qed.

End value_relation.

Section expr_relation.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lam_lang Σ}.

  Context `{genHeapG_inst : !gen_heapG loc lamst.lang.val Σ}.

  Context `{val_ghost_mapG_inst : !ghost_mapG Σ nat val}.
  Context `{loc_ghost_mapG_inst : !ghost_mapG Σ nat loc}.

  Definition exprel_typed (Δ : list (gname * gname)) : typeO -n> exprO -n> lamst.lang.exprO -n> iPropO Σ :=
    λne τ eᵢ eₛ, lift MaybeStuck (valrel_typed Δ τ) eᵢ eₛ.

  Definition open_exprel_typed (Γ : list type) (e : expr) (e' : lamst.lang.expr) (τ : type) :=
    ∀ (Δ : list (gname * gname)) (vs : list val) (vs' : list lamst.lang.val),
      big_sepL3 (fun τ v v' => valrel_typed Δ τ v v') Γ vs vs' ⊢
                exprel_typed Δ τ e.[subst_list_val vs] e'.[lamst.lang.subst_list_val vs'].

End expr_relation.
