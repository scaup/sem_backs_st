From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From st.STLCmuVS Require Import lang typing contexts scopedness logrel.definitions logrel.adequacy logrel.fundamental.
From st.STLCmu Require Import types.
From st.backtranslations.un_syn Require Import universe.base expressions contexts typed.
From st.backtranslations.sem_syn Require Import back_ctx.
From st.backtranslations.sem_syn.syn_le_sem Require Import ctx_syn_le_un.
From st.backtranslations.sem_syn.sem_le_syn Require Import
     gs_ctx ctx_le_gs_ctx ga_ctx gs_ctx_le_ga_ctx ga_ctx_le_ep_ctx.

From st Require Import resources.

Section back_ctx_sem_syn.

  (* Given any semantically typed context, ⊨ C : (Γ;τ) ⇒ ([];1), *)
  Context (C : ctx)
          (Γ : list type) (pΓ : Forall Closed Γ) (τ : type) (pτ : Closed τ)
          (pCscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽) (* Formally, our LR does not enforce well-scopedness, so we add the constraint here explicitly *)
          (pC : ∀ {Σ} {semΣ_inst : semΣ Σ}, ctx_rel_typed MaybeStuck C C Γ τ [] TUnit).

  (* we have a syntactically typed context, C_b, *)
  Definition back_ctx_sem_syn : ctx :=
    back_ctx.back_ctx C Γ τ.

  (* it is indeed syntactically typed of (Γ;τ) ⇒ ([];1): *)
  Lemma back_ctx_sem_syn_typed :
    |C> [] ⊢ₙₒ back_ctx_sem_syn ☾ Γ ; τ ☽ : TUnit.
  Proof. apply back_ctx_typed; auto. Qed.

  (* Furthermore, the backtranslated contexts successfully emulates the original. *)
  (* That is, for all syntactically typed e, Γ ⊢ₙₒ e : τ, C_b[e]⇓ ⇔ C[e]⇓ *)
  Lemma back_ctx_sem_syn_correct_emulation :
    ∀ (e : expr) (de : Γ ⊢ₙₒ e : τ),
      STLCmuVS_halts (fill_ctx (back_ctx_sem_syn) e) <-> STLCmuVS_halts (fill_ctx C e).
  Proof.
    intros e de. split.
    - (* C_b[e] ⇓ ⇒ C[e] *)
      intro SynHalts.
      (* using logical relatedness *)
      apply (exprel_adequate (fill_ctx back_ctx_sem_syn e)); auto.
      intros Σ irisG_inst.
      apply open_exprel_typed_nil'.
      (* using relatedness of contexts *)
      apply rel_back_ctx; auto; try by eapply expr_typed_scoped.
      (* using auto-relatedness of e *)
      by apply auto_related_typed_expr.
    - (* C[e] ⇓ ⇒ C_b[e] *)
      intro SemHalts.
      (* C_s[e] ⇓, where C_s is C wrapped with our VirtStep's *)
      assert (STLCmuVS_halts (fill_ctx (gs_ctx C (length Γ)) e)).
      { (* using logical relatedness *)
        apply (exprel_adequate (fill_ctx C e)); auto.
        intros Σ irisG_inst.
        apply open_exprel_typed_nil'.
        (* using relatedness of contexts *)
        apply (rel_ctx_le_gs_ctx _ _ _ (pC Σ irisG_inst)); auto; try by eapply expr_typed_scoped.
        (* using auto-relatedness of e *)
        by apply auto_related_typed_expr. }
      (* GA(C)[e] ⇓, where GA(C) is C wrapped with our guard's/asserts *)
      assert (STLCmuVS_halts (fill_ctx (ga_ctx C Γ τ) e)).
      { (* using logical relatedness *)
        apply (exprel_adequate (fill_ctx (gs_ctx C (length Γ)) e)); auto.
        intros Σ irisG_inst.
        apply open_exprel_typed_nil'.
        (* using relatedness of contexts *)
        apply rel_gs_ctx_le_ga_ctx; auto; try by eapply expr_typed_scoped.
        (* using auto-relatedness of e *)
        by apply auto_related_typed_expr. }
      { (* using logical relatedness *)
        apply (exprel_adequate (fill_ctx (ga_ctx C Γ τ) e)); auto.
        intros Σ irisG_inst.
        apply open_exprel_typed_nil'.
        (* using relatedness of contexts *)
        apply rel_ga_ctx_le_ep_ctx; auto; try by eapply expr_typed_scoped.
        (* using auto-relatedness of e *)
        by apply auto_related_typed_expr. }
  Qed.

End back_ctx_sem_syn.
