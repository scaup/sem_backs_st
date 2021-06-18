From iris Require Import program_logic.weakestpre.
From st.lamst Require Import lang types typing contexts.
From st.lam Require Import lang wkpre generic.lift contexts contexts_subst.
From st.backtranslations.st_sem Require Import ghost heap_emul.base expressions contexts.
From st.backtranslations.st_sem.well_defined.logrel Require Import definition compat_lemmas compat_lemmas_easy.
From iris.proofmode Require Import tactics.
From st Require Import resources.

Section fundamental_theorem.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  Lemma fundamental (Γ : list lamst.types.type) (e : lamst.lang.expr) (τ : lamst.types.type)
        (d : Γ ⊢ₛₜ e : τ) :
    open_exprel_typed Γ <<e>> <<e>> τ.
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
    - by apply compat_alloc.
    - by apply compat_read.
    - by eapply compat_write.
    - by eapply compat_bind.
    - by apply compat_retrn.
    - by apply compat_runst.
    - by eapply compat_equal.
  Qed.

  Opaque alloc read write bind retrn runst.

  Lemma ctx_item_fundamental (Γ : list lamst.types.type) (τ : lamst.types.type)
        (Γ' : list lamst.types.type) (τ' : lamst.types.type) (Ci : lamst.contexts.ctx_item) (pCi :  lamst.contexts.typed_ctx_item Ci Γ τ Γ' τ') :
    ctx_rel_typed (back_ctx_item Ci) (back_ctx_item Ci) Γ τ Γ' τ'.
  Proof.
    destruct pCi; intros e e' Hee'; simpl.
    - by apply compat_Lam.
    - eapply compat_App; auto; eauto. by apply fundamental.
    - eapply compat_App; auto; eauto. by apply fundamental.
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
    - eapply compat_write; eauto. by apply fundamental.
    - eapply compat_equal; eauto. by apply fundamental.
    - eapply compat_equal; eauto. by apply fundamental.
    - by apply compat_retrn.
    - eapply compat_bind; eauto. by apply fundamental.
    - eapply compat_bind; eauto. by apply fundamental.
    - by apply compat_runst.
  Qed.

  Lemma ctx_fundamental (C : lamst.contexts.ctx) (Γ : list lamst.types.type) (τ : lamst.types.type)
        (Γ' : list lamst.types.type) (τ' : lamst.types.type) :
      lamst.contexts.typed_ctx C Γ τ Γ' τ' →
      ctx_rel_typed (back_ctx C) (back_ctx C) Γ τ Γ' τ'.
  Proof.
    intro H. induction H.
    - simpl. by intros e e' Hee'.
    - simpl. iIntros (e e' Hee' Δ vs vs') "Hvs". rewrite -!fill_ctx_app.
      iApply (ctx_item_fundamental _ _ _ _ k H); auto.
  Qed.

End fundamental_theorem.
