From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From st.backtranslations.st_sem.correctness Require Import
     sem_le_st.logrel.definition sem_le_st.logrel.adequacy sem_le_st.logrel.fundamental
     st_le_sem.logrel.definition st_le_sem.logrel.adequacy st_le_sem.logrel.fundamental.
From st.lam Require Import typing contexts scopedness logrel.definitions logrel.adequacy logrel.fundamental.
From st.lamst Require Import contexts types lang.
From st.backtranslations.st_sem Require Import expressions contexts scoped retraction.
From st.backtranslations.st_sem.well_defined.logrel Require Import definition fundamental matches_sem.
From st.embedding Require Import types expressions typed.
From st.lam Require Import types lang.

From st Require Import resources.

Section back_ctx_st_sem.

  (* Given any syntactically-typed context in lamst, ⊢ₛₜ C : ([[Γ]];[[τ]]) ⇒ ([];1), *)
  Context (C : ctx)
          (Γ : list type) (pΓ : Forall Closed Γ) (τ : type) (pτ : Closed τ)
          (pC : typed_ctx C (embed <$> Γ) (embed τ) [] (embed TUnit)).

  (* we have a semantically typed context, C_b, *)
  Definition back_ctx_st_sem : lam.contexts.ctx :=
    back_ctx C.

  (* It is indeed semantically typed of (Γ;τ) ⇒ ([];1),
     that is, it is auto-related in our logical relation for the semantic language *)
  Lemma back_ctx_st_sem_sem_typed :
    ∀ {Σ} {semΣ_inst : semΣ Σ},
      logrel.definitions.ctx_rel_typed MaybeStuck
                                         back_ctx_st_sem
                                         back_ctx_st_sem
                                           Γ τ [] TUnit.
  Proof.
    intros Σ semΣ_inst.
    assert (ctx_rel_typed
              back_ctx_st_sem
              back_ctx_st_sem
                (embed <$> Γ) (embed τ) [] lamst.types.TUnit).
    { apply ctx_fundamental. apply pC. }
    by apply matches_sem_ctx.
  Qed.

  (* Furthermore, the backtranslated contexts successfully emulates the original (when interacting with syntactically typed terms in lam). *)
  (* That is, for all syntactically typed e, Γ ⊢ₙₒ e : τ, C_b[e]⇓ ⇔ C[[[e]]]⇓ *)

  Lemma back_ctx_st_sem_correct_emulation :
    ∀ (e : expr) (de : Γ ⊢ₙₒ e : τ),
      lam_halts (lam.contexts.fill_ctx back_ctx_st_sem e) <-> lamst_halts (fill_ctx C (embd_expr e)).
  Proof.
    intros e de. split.
    - (* C_b[e] ⇓ ⇒ C[e] ⇓ *)
      intro LamHalts.
      (* using logical relatedness *)
      apply (correctness.sem_le_st.logrel.adequacy.exprel_adequate
               (lam.contexts.fill_ctx back_ctx_st_sem e)); auto.
      (* proving relatedness *)
      intros Σ sem_le_stΣ_inst.
      apply correctness.sem_le_st.logrel.definition.open_exprel_typed_nil'.
      (* using relatedness of context with backtrns *)
      apply (correctness.sem_le_st.logrel.fundamental.ctx_fundamental C (embed <$> Γ) (embed τ)); auto.
      (* using fun thm *)
      rewrite <- (retraction _ _ _ de) at 1.
      apply (correctness.sem_le_st.logrel.fundamental.fundamental); by apply embd_typed.
    - (* C[e] ⇓ ⇒ C_b[e] ⇓ *)
      intro LamSTHalts.
      (* using logical relatedness *)
      apply (correctness.st_le_sem.logrel.adequacy.exprel_adequate
               (fill_ctx C [[e]])); auto.
      (* proving relatedness *)
      intros Σ st_le_semΣ_inst.
      apply correctness.st_le_sem.logrel.definition.open_exprel_typed_nil'.
      (* using relatedness of context with backtrns *)
      apply (correctness.st_le_sem.logrel.fundamental.ctx_fundamental C (embed <$> Γ) (embed τ)); auto.
      (* using fun thm *)
      rewrite <- (retraction _ _ _ de) at 2.
      apply (correctness.st_le_sem.logrel.fundamental.fundamental); by apply embd_typed.
  Qed.

End back_ctx_st_sem.
