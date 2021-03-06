From st.STLCmuVS Require Import lang typing contexts scopedness.
From st.STLCmu Require Import types.
From st.STLCmuST Require Import lang types typing contexts.
From st.embedding Require Import types expressions typed contexts.
From st.thms Require Import pres_ctx_equiv.
From st.backtranslations.st_sem Require Import retraction.
From st.backtranslations.st_sem.correctness Require Import
     sem_le_st.logrel.definition sem_le_st.logrel.adequacy sem_le_st.logrel.fundamental
     st_le_sem.logrel.definition st_le_sem.logrel.adequacy st_le_sem.logrel.fundamental.

Theorem reflection_equiv (Γ : list STLCmu.types.type) (dΓ : Forall Closed Γ) e1 e2 (τ : STLCmu.types.type) (dτ : Closed τ)
  (de1 : Γ ⊢ₙₒ e1 : τ) (de2 : Γ ⊢ₙₒ e2 : τ) :
  STLCmuVS_st_equiv (fmap embed Γ) (embd_expr e1) (embd_expr e2) (embed τ) →
  STLCmuVS_equiv Γ e1 e2 τ.
Proof.
  intro Hequiv. destruct Hequiv as (_ & _ & _ & _ & Hequiv).
  repeat split; auto.
  - intro LamHalts.
    specialize (Hequiv (embd_ctx C) (embd_ctx_typed C _ _ _ _ dC)).
    cut (STLCmuST_halts (fill_ctx (embd_ctx C) [[e2]])).
    { apply st_le_sem.logrel.adequacy.exprel_adequate.
      intros Σ st_le_semΣ.
      cut (@open_exprel_typed Σ st_le_semΣ [] (fill_ctx (embd_ctx C) [[e2]]) (STLCmuVS.contexts.fill_ctx C e2) TUnit).
      { intro H. specialize (H [] [] []). asimpl in H. apply H. }
      rewrite comm_fill_ctx_embd.
      rewrite <- (retraction [] (STLCmuVS.contexts.fill_ctx C e2) STLCmu.types.TUnit) at 2.
      apply st_le_sem.logrel.fundamental.fundamental.
      change [] with (fmap embed []). change TUnit with (embed STLCmu.types.TUnit).
      apply embd_typed. eapply STLCmuVS.contexts.typed_ctx_typed; eauto.
      by eapply STLCmuVS.contexts.typed_ctx_typed.
    }
    apply Hequiv.
    { eapply sem_le_st.logrel.adequacy.exprel_adequate; eauto.
      intros Σ sem_le_stΣ.
      cut (@sem_le_st.logrel.definition.open_exprel_typed Σ sem_le_stΣ [] (STLCmuVS.contexts.fill_ctx C e1) (fill_ctx (embd_ctx C) [[e1]]) TUnit).
      { intro H. specialize (H [] [] []). asimpl in H. apply H. }
      rewrite comm_fill_ctx_embd.
      rewrite <- (retraction [] (STLCmuVS.contexts.fill_ctx C e1) STLCmu.types.TUnit) at 1.
      apply sem_le_st.logrel.fundamental.fundamental.
      change [] with (fmap embed []). change TUnit with (embed STLCmu.types.TUnit).
      apply embd_typed. eapply STLCmuVS.contexts.typed_ctx_typed; eauto.
      by eapply STLCmuVS.contexts.typed_ctx_typed.
    }
  - intro LamSTHalts.
    specialize (Hequiv (embd_ctx C) (embd_ctx_typed C _ _ _ _ dC)).
    cut (STLCmuST_halts (fill_ctx (embd_ctx C) [[e1]])).
    { apply st_le_sem.logrel.adequacy.exprel_adequate.
      intros Σ st_le_semΣ.
      cut (@open_exprel_typed Σ st_le_semΣ [] (fill_ctx (embd_ctx C) [[e1]]) (STLCmuVS.contexts.fill_ctx C e1) TUnit).
      { intro H. specialize (H [] [] []). asimpl in H. apply H. }
      rewrite comm_fill_ctx_embd.
      rewrite <- (retraction [] (STLCmuVS.contexts.fill_ctx C e1)) at 2.
      apply st_le_sem.logrel.fundamental.fundamental.
      change [] with (fmap embed []). change TUnit with (embed STLCmu.types.TUnit).
      apply embd_typed. eapply STLCmuVS.contexts.typed_ctx_typed; eauto.
      by eapply STLCmuVS.contexts.typed_ctx_typed.
    }
    apply Hequiv.
    { eapply sem_le_st.logrel.adequacy.exprel_adequate; eauto.
      intros Σ sem_le_stΣ.
      cut (@sem_le_st.logrel.definition.open_exprel_typed Σ sem_le_stΣ [] (STLCmuVS.contexts.fill_ctx C e2) (fill_ctx (embd_ctx C) [[e2]]) TUnit).
      { intro H. specialize (H [] [] []). asimpl in H. apply H. }
      rewrite comm_fill_ctx_embd.
      rewrite <- (retraction [] (STLCmuVS.contexts.fill_ctx C e2)) at 1.
      apply sem_le_st.logrel.fundamental.fundamental.
      change [] with (fmap embed []). change TUnit with (embed STLCmu.types.TUnit).
      apply embd_typed. eapply STLCmuVS.contexts.typed_ctx_typed; eauto.
      by eapply STLCmuVS.contexts.typed_ctx_typed.
    }
Qed.
