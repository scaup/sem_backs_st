From iris.base_logic.lib Require Import ghost_map.
From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.STLCmuVS Require Import lang wkpre generic.lift contexts scopedness.
From st.STLCmu Require Import types.
From st.prelude Require Import big_op_three.
From st Require Import resources.

Canonical Structure typeO := leibnizO type.

Section definition.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  (* We define a stuckness-sensistive and insensitive one *)
  Context (s : stuckness).

  Fixpoint valrel_typed_gen_pre (Ψ : typeO -n> valO -n> valO -n> iPropO Σ) (τ : typeO) : valO -n> valO -n> iPropO Σ := λne v v',
    (match τ with
     | TUnit => ⌜ v = (()%Vₙₒ : valO) ⌝ ∧ ⌜ v' = (()%Vₙₒ : valO) ⌝
     | TBool => ∃ b : bool, ⌜ v = b ⌝ ∧ ⌜ v' = b ⌝
     | TInt => ∃ z : Z, ⌜ v = z ⌝ ∧ ⌜ v' = z ⌝
     | TProd τ1 τ2 => ∃ v1 v2 v1' v2', ⌜ v = (v1, v2)%Vₙₒ ⌝ ∧ ⌜ v' = (v1' , v2')%Vₙₒ ⌝ ∗ valrel_typed_gen_pre Ψ τ1 v1 v1' ∗ valrel_typed_gen_pre Ψ τ2 v2 v2'
     | TSum τ1 τ2 => ∃ vi vi', (⌜ v = InjLV vi ⌝ ∧ ⌜ v' = InjLV vi' ⌝ ∧ valrel_typed_gen_pre Ψ τ1 vi vi') ∨
                              (⌜ v = InjRV vi ⌝ ∧ ⌜ v' = InjRV vi' ⌝ ∧ valrel_typed_gen_pre Ψ τ2 vi vi')
     | TArrow τ1 τ2 => □ (∀ w w', valrel_typed_gen_pre Ψ τ1 w w' -∗ lift s (valrel_typed_gen_pre Ψ τ2) (v w) (v' w'))
     | TRec τ => ∃ w w', ⌜ v = FoldV w ⌝ ∧ ⌜ v' = FoldV w' ⌝ ∧ ▷ (Ψ τ.[TRec τ/] w w')
     | TVar X => False
     end)%I.

  Definition valrel_typed_gen (Ψ : typeO -n> valO -n> valO -n> iPropO Σ) : typeO -n> valO -n> valO -n> iPropO Σ := λne τ v v', valrel_typed_gen_pre Ψ τ v v'.

  Instance valrel_typed_gen_contractive : Contractive valrel_typed_gen.
  Proof.
    intros n P1 P2 dl. rewrite /valrel_typed_gen. intro τ. simpl.
    induction τ; try by solve_contractive.
    - intros v v'. simpl. do 6 f_equiv. specialize (IHτ1 a a0). simpl in IHτ1. by rewrite IHτ1.
      rewrite /lift. do 5 f_equiv. specialize (IHτ2 a1 a2). simpl in IHτ2. by rewrite IHτ2.
  Qed.

  Definition valrel_typed := fixpoint valrel_typed_gen.

  Lemma valrel_typed_unfold τ v1 v2 : valrel_typed τ v1 v2 ≡ valrel_typed_gen (fixpoint valrel_typed_gen) τ v1 v2.
  Proof. do 3 f_equiv. by rewrite -fixpoint_unfold. Qed.
  Lemma valrel_typed_unfold' τ : valrel_typed τ ≡ valrel_typed_gen (fixpoint valrel_typed_gen) τ.
  Proof. intros x x'. by rewrite valrel_typed_unfold. Qed.
  Lemma valrel_typed_unfold'' : valrel_typed ≡ valrel_typed_gen (fixpoint valrel_typed_gen).
  Proof. intros x. by rewrite valrel_typed_unfold'. Qed.
  Lemma valrel_typed_gen_pre_gen Ψ τ v v' : valrel_typed_gen_pre Ψ τ v v' ≡ valrel_typed_gen Ψ τ v v'.
  Proof. auto. Qed.
  Lemma valrel_typed_gen_pre_gen' Ψ τ : valrel_typed_gen_pre Ψ τ ≡ valrel_typed_gen Ψ τ.
  Proof. intro. intro. auto. Qed.

  Lemma valrel_typed_TUnit_unfold v v' : valrel_typed TUnit v v' ≡ (⌜ v = (()%Vₙₒ : valO) ⌝ ∧ ⌜ v' = (()%Vₙₒ : valO) ⌝)%I.
  Proof. by rewrite valrel_typed_unfold. Qed.
  Lemma valrel_typed_TBool_unfold v v' : valrel_typed TBool v v' ≡ (∃ b : bool, ⌜ v = b ⌝ ∧ ⌜ v' = b ⌝)%I.
  Proof. by rewrite valrel_typed_unfold. Qed.
  Lemma valrel_typed_TInt_unfold v v' : valrel_typed TInt v v' ≡ (∃ z : Z, ⌜ v = z ⌝ ∧ ⌜ v' = z ⌝)%I.
  Proof. by rewrite valrel_typed_unfold. Qed.
  Lemma valrel_typed_TArrow_unfold τ1 τ2 v v' : valrel_typed (TArrow τ1 τ2) v v' ≡ (□ (∀ w w', valrel_typed τ1 w w' -∗ lift s (valrel_typed τ2) (v w) (v' w')))%I.
  Proof.
    rewrite valrel_typed_unfold. rewrite /valrel_typed_gen. simpl.
    f_equiv. f_equiv. intros w. f_equiv. intro w'. f_equiv.
    - rewrite valrel_typed_gen_pre_gen. unfold valrel_typed. rewrite -valrel_typed_unfold. auto.
    - rewrite /lift. f_equiv. simpl. f_equiv. f_equiv. f_equiv. f_equiv.
      by rewrite valrel_typed_unfold.
  Qed.
  Lemma valrel_typed_TSum_unfold τ1 τ2 v v' : valrel_typed (TSum τ1 τ2) v v' ≡ (∃ vi vi', (⌜ v = InjLV vi ⌝ ∧ ⌜ v' = InjLV vi' ⌝ ∧ valrel_typed τ1 vi vi') ∨ (⌜ v = InjRV vi ⌝ ∧ ⌜ v' = InjRV vi' ⌝ ∧ valrel_typed τ2 vi vi'))%I.
  Proof. rewrite valrel_typed_unfold. simpl. repeat f_equiv; rewrite valrel_typed_gen_pre_gen'; rewrite -valrel_typed_unfold'; auto. Qed.
  Lemma valrel_typed_TProd_unfold τ1 τ2 v v' : valrel_typed (TProd τ1 τ2) v v' ≡ (∃ v1 v2 v1' v2', ⌜ v = (v1, v2)%Vₙₒ ⌝ ∧ ⌜ v' = (v1' , v2')%Vₙₒ ⌝ ∗ valrel_typed τ1 v1 v1' ∗ valrel_typed τ2 v2 v2')%I.
  Proof. rewrite valrel_typed_unfold. simpl. repeat f_equiv; rewrite valrel_typed_gen_pre_gen'; rewrite -valrel_typed_unfold'; auto. Qed.
  Lemma valrel_typed_TRec_unfold τ v v' : valrel_typed (TRec τ) v v' ≡ (∃ w w', ⌜ v = FoldV w ⌝ ∧ ⌜ v' = FoldV w' ⌝ ∧ ▷ (valrel_typed τ.[TRec τ/] w w'))%I.
  Proof. rewrite valrel_typed_unfold. simpl. repeat f_equiv; rewrite valrel_typed_gen_pre_gen'; rewrite -valrel_typed_unfold'; auto. Qed.
  Lemma valrel_typed_TVar_unfold X v v' : valrel_typed (TVar X) v v' ≡ False%I.
  Proof. rewrite valrel_typed_unfold. by simpl. Qed.

  Ltac simpl_valrel_typed := fold (valrel_typed_gen_pre); repeat rewrite valrel_typed_gen_pre_gen -valrel_typed_unfold; fold (valrel_typed).

  Global Instance valrel_typed_persistent τ v v' : Persistent (valrel_typed τ v v').
  Proof.
    rewrite /Persistent. revert τ v v'. iLöb as "IHlob". iIntros (τ).
    iInduction τ as [ | | | τ1 τ2 | τ1 τ2 | τ1 τ2 | τ1 τ2 | τ ] "IH";
      iIntros (v v'); rewrite valrel_typed_unfold; try by iIntros "#H".
    - iIntros "H". iDestruct "H" as (v1 v2 v1' v2') "(-> & -> & H1 & H2)". simpl_valrel_typed.
      iExists v1, v2, v1', v2'. simpl_valrel_typed. repeat iSplit; auto. iApply ("IH" with "H1"). iApply ("IH1" with "H2").
    - simpl_valrel_typed. iIntros "H". iDestruct "H" as (vi vi') "[(-> & -> & H1) | (-> & -> & H2)]"; iExists vi, vi'; simpl_valrel_typed.
      + iLeft. repeat iSplit; auto. by iApply ("IH" with "H1").
      + iRight. repeat iSplit; auto. by iApply ("IH1" with "H2").
    - iIntros "H". iDestruct "H" as (w w') "(-> & -> & H)". simpl_valrel_typed. iExists w, w'. repeat iSplitL ""; auto.
      iApply bi.later_persistently_1. iNext. by iApply "IHlob".
  Qed.

  Definition exprel_typed : typeO -n> exprO -n> exprO -n> iPropO Σ := λne τ eᵢ eₛ, lift s (valrel_typed τ) eᵢ eₛ.

  Definition open_exprel_typed (Γ : list type) (e e' : expr) (τ : type) :=
    ∀ (vs vs' : list val), big_sepL3 (fun τ v v' => valrel_typed τ v v') Γ vs vs' ⊢
                                     exprel_typed τ e.[subst_list_val vs] e'.[subst_list_val vs'].

  Lemma open_exprel_typed_nil τ e e' : (⊢ exprel_typed τ e e') -> open_exprel_typed [] e e' τ.
  Proof. iIntros (Hee' vs vs') "Hvv'". destruct vs, vs'; auto. asimpl. iApply Hee'. Qed.

  Lemma open_exprel_typed_nil' τ e e' : open_exprel_typed [] e e' τ → (⊢ exprel_typed τ e e').
  Proof. rewrite /open_exprel_typed. iIntros (Hee'). iDestruct (Hee' [] []) as "H". asimpl. by iApply "H". Qed.

  Definition ctx_item_rel_typed (Ci Ci' : ctx_item) Γ τ Γ' τ' :=
    ∀ e e' (pe : expr_scoped (length Γ) e) (pe' : expr_scoped (length Γ) e'), open_exprel_typed Γ e e' τ → open_exprel_typed Γ' (fill_ctx_item Ci e) (fill_ctx_item Ci' e') τ'.

  Definition ctx_rel_typed (C C' : ctx) Γ τ Γ' τ' :=
    ∀ e e' (pe : expr_scoped (length Γ) e) (pe' : expr_scoped (length Γ) e'), open_exprel_typed Γ e e' τ → open_exprel_typed Γ' (fill_ctx C e) (fill_ctx C' e') τ'.

End definition.

Ltac unfold_valrel_typed :=
  (rewrite valrel_typed_TUnit_unfold) ||
  (rewrite valrel_typed_TBool_unfold) ||
  (rewrite valrel_typed_TInt_unfold) ||
  (rewrite valrel_typed_TArrow_unfold) ||
  (rewrite valrel_typed_TSum_unfold) ||
  (rewrite valrel_typed_TProd_unfold) ||
  (rewrite valrel_typed_TRec_unfold).

Ltac simpl_valrel_typed := fold (valrel_typed_gen_pre); repeat rewrite valrel_typed_gen_pre_gen -valrel_typed_unfold; fold (valrel_typed).
