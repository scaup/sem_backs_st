From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export ghost_map.
From st.lam Require Import lang types typing contexts logrel.definitions contexts scopedness.
From st.lamst Require Import types contexts.
From st.backtranslations.st_sem Require Import expressions retraction contexts scoped.
From st.backtranslations.st_sem.well_defined.logrel Require Import definition fundamental matches_sem.
From st.embedding Require Import types expressions typed.
From st Require Import resources.

Notation ctx_sem_typed C C' Γ τ Γ' τ' :=
  (∀ Σ {semΣ_inst : semΣ Σ},
      @lam.logrel.definitions.ctx_rel_typed Σ semΣ_inst MaybeStuck C C' Γ τ Γ' τ'
  ).

Notation ctx_rel_st_typed C C' Γ τ Γ' τ' :=
  (∀ Σ {semΣ_inst : semΣ Σ},
     @well_defined.logrel.definition.ctx_rel_typed Σ semΣ_inst C C' Γ τ Γ' τ').

Definition uni_back_ctx (C : lamst.contexts.ctx) : lam.contexts.ctx :=
  back_ctx C.

Lemma uni_back_ctx_sem_typed (C : lamst.contexts.ctx) (Γ : list lam.types.type) (τ : lam.types.type)
  (H : lamst.contexts.typed_ctx C (fmap embed Γ) (embed τ) [] (embed lam.types.TUnit)) :
  ctx_sem_typed (uni_back_ctx C) (uni_back_ctx C) Γ τ [] lam.types.TUnit.
Proof.
  assert (ctx_rel_st_typed (uni_back_ctx C) (uni_back_ctx C) (map embed Γ) (embed τ) [] lamst.types.TUnit).
  { intros Σ semΣ_inst. apply ctx_fundamental. apply H. }
  intros Σ semΣ_inst. eapply (@matches_sem_ctx Σ semΣ_inst (uni_back_ctx C) (uni_back_ctx C) Γ τ [] lam.types.TUnit).
  apply H0.
Qed.

Lemma uni_back_ctx_scoped (C : lamst.contexts.ctx) (Γ : list lam.types.type) (τ : lam.types.type)
  (H : lamst.contexts.typed_ctx C (fmap embed Γ) (embed τ) [] (embed lam.types.TUnit)) :
  |sC> 0 ⊢ₙₒ uni_back_ctx C ☾ length Γ ☽.
Proof.
  pose proof (back_ctx_scope _ _ _ _ _ H). rewrite /uni_back_ctx.
  by rewrite /= fmap_length in H0.
Qed.

From st.lamst Require Import lang.
From st.backtranslations.st_sem.correctness Require Import
     sem_le_st.logrel.definition sem_le_st.logrel.adequacy sem_le_st.logrel.fundamental
     st_le_sem.logrel.definition st_le_sem.logrel.adequacy st_le_sem.logrel.fundamental.

Lemma uni_back_ctx_correct (C : lamst.contexts.ctx) (Γ : list lam.types.type) (τ : lam.types.type)
  (H : lamst.contexts.typed_ctx C (fmap embed Γ) (embed τ) [] (embed lam.types.TUnit)) :
  ∀ (e : lam.lang.expr) (de : lam.typing.typed Γ e τ),
    lam_halts (lam.contexts.fill_ctx (uni_back_ctx C) e) <-> lamst_halts (lamst.contexts.fill_ctx C (embd_expr e)).
Proof.
  intros e de. split.
  - (* semantic ≤ st *) intro SemHalt.
    (* using logical relation to prove refinement *)
    apply (correctness.sem_le_st.logrel.adequacy.exprel_adequate
             (lam.contexts.fill_ctx (uni_back_ctx C) e)); auto.
    (* proving relatedness *)
    { intros Σ sem_le_stΣ_inst. simpl in H. rewrite /uni_back_ctx.
      pose proof (embd_typed _ _ _ de) as de'.
      pose proof (correctness.sem_le_st.logrel.fundamental.fundamental _ _ _ de') as sem_e.
      rewrite retraction in sem_e.
      pose proof (correctness.sem_le_st.logrel.fundamental.ctx_fundamental C _ _ _ _ H e [[e]] sem_e).
      iDestruct (H0 [] [] []) as "H0". asimpl. by iApply "H0".
    }
  - (* st ≤ semantic *) intro StHalt.
    (* using logical relation to prove refinement *)
    apply (correctness.st_le_sem.logrel.adequacy.exprel_adequate
             (lamst.contexts.fill_ctx C [[e]])); auto.
    (* proving relatedness *)
    { intros Σ st_le_semΣ_inst. simpl in H. rewrite /uni_back_ctx.
      pose proof (embd_typed _ _ _ de) as de'.
      pose proof (correctness.st_le_sem.logrel.fundamental.fundamental _ _ _ de') as sem_e.
      rewrite retraction in sem_e.
      pose proof (correctness.st_le_sem.logrel.fundamental.ctx_fundamental C _ _ _ _ H [[e]] e sem_e).
      iDestruct (H0 [] [] []) as "H0". asimpl. by iApply "H0".
    }
Qed.
