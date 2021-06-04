From st.prelude Require Import autosubst.
From st.lam Require Import types nr_types lang typing tactics.
From st.lam.lib Require Import fixlam omega universe.base.

Inductive direction :=
  | Embed
  | Project.

Definition FstSnd (ep : direction) : expr → expr :=
  match ep with
  | Embed => Fst
  | Project => Snd
  end.

Definition opp_direction (ep : direction) :=
  match ep with
  | Embed => Project
  | Project => Embed
  end.

Fixpoint ep_pair (τ : nr_type) (dir : direction) : val :=
  (match τ with
   | NRTUnit => match dir with
             | Embed => inject TCUnit
             | Project => extract TCUnit
             end
   | NRTBool => match dir with
             | Embed => inject TCBool
             | downward => extract TCBool
             end
   | NRTInt => match dir with
            | Embed => inject TCInt
            | Project => extract TCInt
            end
   | NRTProd τ1 τ2 => match dir with
                   | Embed => LamV (LetIn (Fst %0)
                                        (LetIn (Snd %1)
                                               (inject TCProd ((ep_pair τ1 Embed).{ren (+3)} %1, (ep_pair τ2 Embed).{ren (+3)} %0))))
                   | Project => LamV (LetIn (extract TCProd %0)
                                          (LetIn (Fst %0)
                                                 (LetIn (Snd %1)
                                                        ((ep_pair τ1 Project).{ren (+4)} %1 , (ep_pair τ2 Project).{ren (+4)} %0))))
     end
   | NRTSum τ1 τ2 => match dir with
                  | Embed => LamV (Case %0
                                      (inject TCSum (InjL ((ep_pair τ1 Embed).{ren (+2)} %0)))
                                      (inject TCSum (InjR ((ep_pair τ2 Embed).{ren (+2)} %0))))
                  | Project => LamV (Case (extract TCSum %0)
                                        (InjL ((ep_pair τ1 Project).{ren (+2)} %0))
                                        (InjR ((ep_pair τ2 Project).{ren (+2)} %0)))
                  end
   | NRTArrow τ1 τ2 => match dir with
                    | Embed => LamV (inject TCArrow (Lam ((ep_pair τ2 Embed).{ren (+2)} (%1 ((ep_pair τ1 Project).{ren (+2)} %0)))))
                    | Project => LamV (Lam ((ep_pair τ2 Project).{ren (+2)} (extract TCArrow %1 ((ep_pair τ1 Embed).{ren (+2)} %0))))
                    end
  end)%Eₙₒ.

Definition direction_type dir (τ : nr_type) :=
  match dir with
  | Embed => TArrow τ TUniverse
  | Project => TArrow TUniverse τ
  end.

Lemma ep_pair_typed (τ : nr_type) (dir : direction) :
  ∀ Γ, Γ ⊢ₙₒ (ep_pair τ dir) : (direction_type dir τ).
Proof.
  generalize dependent dir.
  induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 ];
    intros dir; try by (destruct dir; (apply inject_typed || apply extract_typed)).
  - (* TProd *) destruct dir.
    + repeat (fold nr_type_type; fold ep_pair; ((rewrite -val_subst_valid; apply context_weakening3) || apply IHτ1 with (dir := Embed) || apply IHτ2 with (dir := Embed) || apply inject_typed || econstructor)).
    + repeat (fold nr_type_type ep_pair; ((rewrite -val_subst_valid; apply context_weakening4) || apply IHτ1 with (dir := Project) || apply IHτ2 with (dir := Project) || apply (extract_typed TCProd) || econstructor)).
  - (* TSum *) destruct dir.
    + repeat ((rewrite -val_subst_valid; apply context_weakening2) || apply IHτ1 with (dir := Embed) || apply IHτ2 with (dir := Embed) || closed_solver || apply inject_typed || econstructor).
    + repeat ((rewrite -val_subst_valid; apply context_weakening2) || apply IHτ1 with (dir := Project) || apply IHτ2 with (dir := Project) || closed_solver || apply (extract_typed TCSum) || econstructor).
  - (* TArrow *) destruct dir.
    + repeat ((rewrite -val_subst_valid; apply context_weakening2) || apply IHτ1 with (dir := Project) || apply IHτ2 with (dir := Embed) || closed_solver || apply inject_typed || econstructor).
    + repeat ((rewrite -val_subst_valid; apply context_weakening2) || apply IHτ1 with (dir := Embed) || apply IHτ2 with (dir := Project) || closed_solver || apply (extract_typed TCArrow) || econstructor).
Qed.
