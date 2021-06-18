From st.prelude Require Import autosubst.
From st.lam Require Import nr_types scopedness types lang typing tactics.

Inductive action :=
  | Guard
  | Assert.

Definition FstSndga (ga : action) : expr → expr :=
  match ga with
  | Guard => Fst
  | Assert => Snd
  end.

Definition opp_action (ga : action) :=
  match ga with
  | Guard => Assert
  | Assert => Guard
  end.

Fixpoint ga_pair (τ : nr_type) (ga : action) : val :=
  (match τ with
   | NRTUnit => match ga with
             | Guard => LamV %0
             | Assert => LamV (Seq %0 ())
             end
   | NRTBool => match ga with
             | Guard => LamV %0
             | Assert => LamV (If %0 true false)
             end
   | NRTInt => match ga with
            | Guard => LamV %0
            | Assert => LamV (%0 + 0)
            end
   | NRTProd τ1 τ2 => LamV (LetIn (Fst %0) (LetIn (Snd %1) ((ga_pair τ1 ga).{ren (+3)} %1, (ga_pair τ2 ga).{ren (+3)} %0)))
   | NRTSum τ1 τ2 => LamV (Case %0 (InjL ((ga_pair τ1 ga).{ren (+2)} %0)) (InjR ((ga_pair τ2 ga).{ren (+2)} %0)))
   | NRTArrow τ1 τ2 => LamV (Lam ((ga_pair τ2 ga).{ren (+2)} (%1 ((ga_pair τ1 (opp_action ga)).{ren (+2)} %0))))
   end)%Eₙₒ.

(* We never actually need typedness of ga; but it serves as a good sanity check *)
Lemma ga_typed_gen (τ : nr_type) (ga : action) :
  ∀ Γ, Γ ⊢ₙₒ (ga_pair τ ga) : (τ ⟶ τ).
Proof.
  generalize dependent ga.
  induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 ]; intros ga;
    try by (destruct ga; by repeat econstructor).
  - repeat econstructor; fold nr_type_type ga_pair.
    rewrite -val_subst_valid. apply context_weakening3. apply IHτ1.
    rewrite -val_subst_valid. apply context_weakening3. apply IHτ2.
  - repeat econstructor; fold nr_type_type ga_pair.
    rewrite -val_subst_valid. apply context_weakening2. apply IHτ1.
    rewrite -val_subst_valid. apply context_weakening2. apply IHτ2.
  - repeat econstructor; fold nr_type_type ga_pair.
    rewrite -val_subst_valid. apply context_weakening2. apply IHτ2.
    rewrite -val_subst_valid. apply context_weakening2. apply IHτ1.
Qed.

Lemma ga_pair_Closed τ ga :
  Closed (of_val $ ga_pair τ ga).
Proof. apply expr_Closed_n. eapply (expr_typed_scoped []). apply ga_typed_gen. Qed.
