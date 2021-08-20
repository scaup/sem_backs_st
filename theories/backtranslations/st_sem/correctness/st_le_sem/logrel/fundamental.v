From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.

Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

From st.prelude Require Import big_op_three.

From st.lam Require Import lang contexts.
From st.STLCmuST Require Import wkpre lang types typing contexts.

From st.backtranslations.st_sem Require Import expressions ghost heap_emul.base contexts.
From st.backtranslations.st_sem.correctness.st_le_sem.logrel Require Import lift definition compat_lemmas compat_lemmas_easy.
From st Require Import resources.

Section fundamental_theorem.

  Context `{Σ : !gFunctors} `{st_le_semΣ_inst : !st_le_semΣ Σ}.

  Opaque encode alloc read write bind retrn.

  Lemma fundamental (Γ : list STLCmuST.types.type) (e : STLCmuST.lang.expr) (τ : STLCmuST.types.type)
        (d : Γ ⊢ₛₜ e : τ) :
    open_exprel_typed Γ e <<e>> τ.
  Proof.
    induction d; simpl.
    - by apply compat_Var.
    - by apply compat_Unit.
    - by apply compat_Bool.
    - by apply compat_Int.
    - by apply compat_BinOp.
    - by apply compat_Seq.
    - by apply compat_Pair.
    - by eapply compat_Fst.
    - by eapply compat_Snd.
    - by eapply compat_InjL.
    - by eapply compat_InjR.
    - by eapply compat_Case.
    - by eapply compat_If.
    - by eapply compat_LetIn.
    - by eapply compat_Lam.
    - eapply compat_App. apply IHd1. apply IHd2.
    - by eapply compat_Fold.
    - by eapply compat_Unfold.
      (* !! intersting ones !! *)
    - by apply compat_alloc.
    - by apply compat_read.
    - by eapply compat_write.
    - by eapply compat_bind.
    - by apply compat_retrn.
    - by apply compat_runst.
    - by eapply compat_compare.
  Qed.

  Lemma ctx_item_fundamental (Γ : list STLCmuST.types.type) (τ : STLCmuST.types.type)
        (Γ' : list STLCmuST.types.type) (τ' : STLCmuST.types.type) (Ci : STLCmuST.contexts.ctx_item) (pCi :  STLCmuST.contexts.typed_ctx_item Ci Γ τ Γ' τ') :
    ctx_rel_typed [Ci] (back_ctx_item Ci) Γ τ Γ' τ'.
  Proof.
    destruct pCi; intros e e' Hee'; simpl.
    - by apply compat_Lam.
    - eapply compat_App; auto; eauto. by apply fundamental.
    - eapply compat_App. by apply fundamental. auto.
    - eapply compat_LetIn; eauto. by apply fundamental.
    - eapply compat_LetIn; eauto. by apply fundamental.
    - apply compat_Pair; auto. by apply fundamental.
    - apply compat_Pair; auto. by apply fundamental.
    - by eapply compat_Fst.
    - by eapply compat_Snd.
    - by eapply compat_InjL.
    - by eapply compat_InjR.
    - eapply compat_Case; eauto; by apply fundamental.
    - eapply compat_Case; eauto; by apply fundamental.
    - eapply compat_Case; eauto; by apply fundamental.
    - apply compat_If; eauto; by apply fundamental.
    - apply compat_If; auto; by apply fundamental.
    - apply compat_If; auto; by apply fundamental.
    - eapply compat_BinOp; eauto. by apply fundamental.
    - eapply compat_BinOp; eauto. by apply fundamental.
    - by apply compat_Fold.
    - by apply compat_Unfold.
    - by apply compat_alloc.
    - by apply compat_read.
    - eapply compat_write; eauto. by apply fundamental.
    - eapply compat_write. by apply fundamental. eauto.
    - eapply compat_compare. eauto. by apply fundamental.
    - eapply compat_compare; eauto. by apply fundamental.
    - by apply compat_retrn.
    - eapply compat_bind; eauto. by apply fundamental.
    - eapply compat_bind. by apply fundamental. auto.
    - by apply compat_runst.
  Qed.

  Lemma ctx_fundamental (C : STLCmuST.contexts.ctx) (Γ : list STLCmuST.types.type) (τ : STLCmuST.types.type)
        (Γ' : list STLCmuST.types.type) (τ' : STLCmuST.types.type) :
      STLCmuST.contexts.typed_ctx C Γ τ Γ' τ' →
      ctx_rel_typed C (back_ctx C) Γ τ Γ' τ'.
  Proof.
    intro H. induction H.
    - simpl. by intros e e' Hee'.
    - simpl. iIntros (e e' Hee' Δ vs vs') "Hvs". change (k :: K) with ([k] ++ K). rewrite -lam.contexts.fill_ctx_app -STLCmuST.contexts.fill_ctx_app.
      iApply (ctx_item_fundamental _ _ _ _ k H); auto.
  Qed.

End fundamental_theorem.
