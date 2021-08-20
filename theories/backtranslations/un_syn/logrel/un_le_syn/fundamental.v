From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.STLCmuVS Require Import lang scopedness wkpre generic.lift reducibility tactics contexts.
From st.STLCmu Require Import types.
From st.backtranslations.un_syn Require Import logrel.definitions expressions contexts universe.base universe.paths un_le_syn.compat_lemmas.

Section un_le_syn.

  Instance rfn : refinement := un_le_syn.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG STLCmuVS_lang Σ}.

  Lemma universe_back_expr_in_relation n (e : expr) (pne : expr_scoped n e) :
    open_exprel n e (universe_back_expr e).
  Proof.
    induction pne.
    - by apply compat_Var.
    - by apply compat_LetIn.
    - by apply compat_Lam.
    - by apply compat_App.
    - by apply compat_Lit.
    - by apply compat_BinOp.
    - by apply compat_If.
    - by apply compat_Seq.
    - by apply compat_Pair.
    - by apply compat_Fst.
    - by apply compat_Snd.
    - by apply compat_InjL.
    - by apply compat_InjR.
    - by apply compat_Case.
    - by apply compat_Fold.
    - by apply compat_Unfold.
    - by apply compat_VirtStep.
  Qed.

  Lemma universe_back_ctx_item_in_relation n m (Ci : ctx_item) (pCi : ctx_item_scoped Ci n m) :
    ctx_rel n m [Ci] (universe_back_ctx_item Ci).
  Proof.
    destruct pCi; intros e e' Hee'; simpl.
    - by apply compat_Lam.
    - apply compat_App; auto. by apply universe_back_expr_in_relation.
    - apply compat_App; auto. by apply universe_back_expr_in_relation.
    - apply compat_LetIn; auto. by apply universe_back_expr_in_relation.
    - apply compat_LetIn; auto. by apply universe_back_expr_in_relation.
    - apply compat_Pair; auto. by apply universe_back_expr_in_relation.
    - apply compat_Pair; auto. by apply universe_back_expr_in_relation.
    - by apply compat_Fst.
    - by apply compat_Snd.
    - by apply compat_InjL.
    - by apply compat_InjR.
    - apply compat_Case; auto; by apply universe_back_expr_in_relation.
    - apply compat_Case; auto; by apply universe_back_expr_in_relation.
    - apply compat_Case; auto; by apply universe_back_expr_in_relation.
    - apply compat_BinOp; auto. by apply universe_back_expr_in_relation.
    - apply compat_BinOp; auto. by apply universe_back_expr_in_relation.
    - apply compat_If; auto; by apply universe_back_expr_in_relation.
    - apply compat_If; auto; by apply universe_back_expr_in_relation.
    - apply compat_If; auto; by apply universe_back_expr_in_relation.
    - by apply compat_Fold.
    - by apply compat_Unfold.
    - by apply compat_VirtStep.
  Qed.

  Lemma universe_back_ctx_in_relation n m (C : ctx) (pC : ctx_scoped C n m) :
    ctx_rel n m C (universe_back_ctx C).
  Proof.
    induction pC.
    - by intros e e' Hee'.
    - simpl. change (k :: K) with ([k] ++ K).
      eapply (ctx_rel_app _ _ _ [k] (universe_back_ctx_item k) K (universe_back_ctx K)); eauto.
      by apply universe_back_ctx_item_in_relation.
  Qed.

End un_le_syn.
