From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From st.lam Require Import lang typing types nr_types contexts scopedness logrel.definitions adequacy.
From st.backtranslations.un_syn Require Import universe.base expressions contexts typed.
From st.backtranslations.sem_syn Require Import uni_back_ctx ctx_sem_le_syn_add_no_op ctx_syn_le_un ctx_un_le_syn.
From st Require Import resources.

Opaque uni_back_ctx_nil uni_back_ctx_cons.

Definition uni_back_ctx (C : ctx) (Γ : list nr_type) (τ : nr_type) : ctx :=
  match (length Γ) with
  | 0 => uni_back_ctx_nil C τ
  | S n => uni_back_ctx_cons C Γ τ
  end.

Lemma uni_back_ctx_typed (C : ctx) (Γ : list nr_type) (τ : nr_type)
  (H : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽) :
  |C> [] ⊢ₙₒ (uni_back_ctx C Γ τ) ☾ map nr_type_type Γ ; τ ☽ : TUnit.
Proof.
  destruct (length Γ) eqn:eq.
  - rewrite (nil_length_inv _ eq) /=. by apply uni_back_ctx_nil_typed.
  - rewrite /uni_back_ctx eq. apply uni_back_ctx_cons_typed. by rewrite eq.
Qed.

Lemma uni_back_ctx_correct (C : ctx) (Γ : list nr_type) (τ : nr_type)
      (Cscp : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽) (Csem : ∀ {Σ} {semΣ_inst : semΣ Σ}, ctx_rel_typed MaybeStuck C C (fmap nr_type_type Γ) τ [] TUnit) :
  ∀ (e : expr) (de : typed (fmap nr_type_type Γ) e τ),
    lam_halts (fill_ctx (uni_back_ctx C Γ τ) e) <-> lam_halts (fill_ctx C e).
Proof.
  intros e de. split.
  - (* syntactic ≤ semantic *) intro SynHalt.
    apply (exprel_adequate (fill_ctx (uni_back_ctx C Γ τ) e)); auto.
    intros Σ irisG_inst. rewrite /uni_back_ctx.
    destruct (length Γ) eqn:eq.
    + (* project 1 (<<C>> [embed τ [ e ]]) ≤ C [ e ] *) destruct Γ; [|by inversion eq].
      iApply rel_uni_back_ctx_nil_e_le_ctx_e; auto.
    + (* let f = λΓ.e in (<<C>> [embed τ [ f (project τ₁ x₁, ..., project τₘ xₘ) ]]) ≤ C [ e ] *)
      iApply rel_uni_back_ctx_cons_e_le_ctx_e; try rewrite eq; auto.
  - (* semantic ≤ syntactic *) intro SemHalts.
    rewrite /uni_back_ctx. destruct (length Γ) eqn:eq; [destruct Γ; [|by inversion eq]|].
    + (* C [ e ] ≤ project 1 (<<C>> [embed τ [ e ]]) *)
      assert (lam_halts (fill_ctx (C_wrapped_0 C τ) e)).
      * (* C [ e ] ≤ assert 1 (C [guard τ [ e ]]) *)
        apply (exprel_adequate (fill_ctx C e)); auto.
        intros Σ irisG_inst. iApply rel_C_e_le_C_wrapped_0_e; auto.
      * (* assert 1 (C [guard τ [ e ]]) ≤ project 1 (<<C>> [embed τ [ e ]])*)
        apply (exprel_adequate (fill_ctx (C_wrapped_0 C τ) e)); auto.
        intros Σ irisG_inst. iApply rel_C_wrapped_0_e_le_uni_back_ctx_nil_e; auto.
    + (* C [ e ] ≤ λΓ.e in project 1 (C [embed τ [ f (project τ₁ x₁, ..., project τₘ xₘ) ]]) *)
      assert (lam_halts (fill_ctx (C_wrapped_S_n C Γ τ) e)).
      * (* C [ e ] ≤ let f = λΓ.e in (<<C>> [guard τ [ f (assert τ₁ x₁, ..., assert τₘ xₘ) ]]) *)
        apply (exprel_adequate (fill_ctx C e)); auto.
        intros Σ irisG_inst. iApply rel_C_e_le_C_wrapped_S_n_e; try rewrite eq; auto.
      * (* let f = λΓ.e in (<<C>> [guard τ [ f (assert τ₁ x₁, ..., assert τₘ xₘ) ]]) ≤
           let f = λΓ.e in (<<C>> [embed τ [ f (project τ₁ x₁, ..., project τₘ xₘ) ]]) *)
        apply (exprel_adequate (fill_ctx (C_wrapped_S_n C Γ τ) e)); auto.
        intros Σ irisG_inst. iApply rel_C_wrapped_S_n_e_le_uni_back_ctx_cons_e; try rewrite eq; auto.
Qed.
