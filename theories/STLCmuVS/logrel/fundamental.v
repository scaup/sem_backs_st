From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.STLCmuVS Require Import lang types typing wkpre generic.lift contexts logrel.definitions logrel.compat_lemmas contexts scopedness.
From st.prelude Require Import big_op_three.
From st Require Import resources.

Canonical Structure typeO := leibnizO type.

Section definition.

  Context `{Σ : !gFunctors} `{semΣ_inst : !semΣ Σ}.

  (* We define a stuckness-sensistive and insensitive one *)
  Context (s : stuckness).

  Lemma auto_related_typed_expr Γ (e : expr) τ (pe : typed Γ e τ) :
    open_exprel_typed s Γ e e τ.
  Proof.
    induction pe.
    - by apply compat_Var.
    - by apply compat_Unit.
    - by apply compat_Bool.
    - by apply compat_Int.
    - by apply compat_BinOp.
    - by apply compat_Seq.
    - by apply compat_Pair.
    - by eapply compat_Fst.
    - by eapply compat_Snd.
    - by apply compat_InjL.
    - by apply compat_InjR.
    - by eapply compat_Case.
    - by apply compat_If.
    - by eapply compat_LetIn.
    - by apply compat_Lam.
    - by eapply compat_App.
    - by apply compat_Fold.
    - by apply compat_Unfold.
  Qed.

  Lemma auto_related_ctx_item_typed Γ τ Γ' τ' (Ci : ctx_item) (pCi :  typed_ctx_item Ci Γ τ Γ' τ') :
    ctx_item_rel_typed s Ci Ci Γ τ Γ' τ'.
  Proof.
    destruct pCi; intros e e' pe pe' Hee'; simpl.
    - by apply compat_Lam.
    - eapply compat_App; auto; eauto. by apply auto_related_typed_expr.
    - eapply compat_App; eauto. by apply auto_related_typed_expr.
    - eapply compat_LetIn; eauto. by apply auto_related_typed_expr.
    - eapply compat_LetIn; eauto. by apply auto_related_typed_expr.
    - apply compat_Pair; auto. by apply auto_related_typed_expr.
    - apply compat_Pair; auto. by apply auto_related_typed_expr.
    - by eapply compat_Fst.
    - by eapply compat_Snd.
    - by eapply compat_InjL.
    - by eapply compat_InjR.
    - eapply compat_Case; eauto; by apply auto_related_typed_expr.
    - eapply compat_Case; eauto; by apply auto_related_typed_expr.
    - eapply compat_Case; eauto; by apply auto_related_typed_expr.
    - apply compat_If; eauto; by apply auto_related_typed_expr.
    - apply compat_If; auto; by apply auto_related_typed_expr.
    - apply compat_If; auto; by apply auto_related_typed_expr.
    - eapply compat_BinOp; eauto. by apply auto_related_typed_expr.
    - eapply compat_BinOp; eauto. by apply auto_related_typed_expr.
    - by apply compat_Fold.
    - by apply compat_Unfold.
  Qed.

  Lemma auto_related_ctx_typed Γ τ Γ' τ' (C : ctx) (pC : typed_ctx C Γ τ Γ' τ') :
    ctx_rel_typed s C C Γ τ Γ' τ'.
  Proof.
    induction pC.
    - by intros e e' Hee'.
    - intros e e' pe pe' Hee'. simpl. apply (auto_related_ctx_item_typed _ _ _ _ k H).
      eapply scoped_ctx_fill. eauto. by eapply ctx_typed_scoped.
      eapply scoped_ctx_fill. eauto. by eapply ctx_typed_scoped.
      by apply IHpC.
  Qed.

End definition.
