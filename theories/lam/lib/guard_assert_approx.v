From st.prelude Require Import autosubst.
From st.lam Require Import types lang typing tactics.
From st.lam.lib Require Import fixlam omega universe.base.

Inductive action :=
  | Guard
  | Assert.

Definition opp_action (act : action) :=
  match act with
  | Guard => Assert
  | Assert => Guard
  end.

Section guard_assert.

  Local Notation "( x ; y )" := (existT x y) (at level 0, format "( x ;  '/  ' y )").

  Inductive lt_type : type → type → Prop :=
    | lt_TProd_l τ1 τ2 : lt_type τ1 (TProd τ1 τ2)
    | lt_TProd_r τ1 τ2 : lt_type τ2 (TProd τ1 τ2)
    | lt_TSum_l τ1 τ2 : lt_type τ1 (TSum τ1 τ2)
    | lt_TSum_r τ1 τ2 : lt_type τ2 (TSum τ1 τ2)
    | lt_TArrow_l τ1 τ2 : lt_type τ1 (TArrow τ1 τ2)
    | lt_TArrow_r τ1 τ2 : lt_type τ2 (TArrow τ1 τ2)
    | lt_TRec τb : lt_type τb (TRec τb).

  Require Import FunInd Recdef.
  From Coq.Wellfounded Require Import Lexicographic_Product Union.
  From Coq.Relations Require Import Relation_Operators.
  From Coq.Program Require Import Wf.

  Function ga_pair (nτ : { n : nat & type}) (act : action) {wf (lexprod nat (fun _ => type) lt (fun _ => lt_type)) nτ } : val :=
    match nτ with
    | (n;τ) =>
      match n with
      | O => LamV (Var 0)
      | S x => (match τ with
               | TUnit => match act with
                         | Guard => LamV %0
                         | Assert => LamV (Seq %0 ())
                         end
               | TBool => match act with
                         | Guard => LamV %0
                         | Assert => LamV (If %0 true false)
                         end
               | TInt => match act with
                        | Guard => LamV %0
                        | Assert => LamV (%0 + 0)
                        end
               | TProd τ1 τ2 => LamV (LetIn (Fst %0) (LetIn (Snd %1) ((ga_pair (n;τ1) act).{ren (+3)} %1, (ga_pair (n;τ2) act).{ren (+3)} %0)))
               | TSum τ1 τ2 => LamV (Case %0 (InjL ((ga_pair (n;τ1) act).{ren (+2)} %0)) (InjR ((ga_pair (n;τ2) act).{ren (+2)} %0)))
               | TArrow τ1 τ2 => LamV (Lam ((ga_pair (n;τ2) act).{ren (+2)} (%1 ((ga_pair (n;τ1) (opp_action act)).{ren (+2)} %0))))
               | TRec τb => LamV (Fold (ga_pair (x;τb.[TRec τb/]) act (Unfold %0)))
               | TVar X => ()%Vₙₒ
               end)%Eₙₒ
      end
    end.

  1-7: by (intros; apply right_lex; simplify_eq; constructor) || (by intros; apply left_lex ; lia).
  apply wf_lexprod. apply lt_wf. intros _. intro τ. apply Acc_intro. induction τ; try by intros τ' abs; inversion abs.
  Defined.

  Lemma ga_typed_gen (n : nat) (τ : type) (pCτ : Closed_n 0 τ) (act : action) :
    ∀ Γ, Γ ⊢ₙₒ (ga_pair (n;τ) act) : (τ ⟶ τ).
  Proof.
    generalize dependent act.
    generalize dependent τ.
    induction n.
    - intros τ pCτ act Γ. rewrite ga_pair_equation. by repeat econstructor.
    - intros τ.
      induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τb IHτb | X ];
        intros pCτ act; rewrite ga_pair_equation; simpl; try by destruct act; repeat econstructor.
      + repeat econstructor; fold ga_pair.
        rewrite -val_subst_valid. apply context_weakening3. apply IHτ1. closed_solver.
        rewrite -val_subst_valid. apply context_weakening3. apply IHτ2. closed_solver.
      + repeat econstructor; fold ga_pair.
        rewrite -val_subst_valid. apply context_weakening2. apply IHτ1. closed_solver.
        rewrite -val_subst_valid. apply context_weakening2. apply IHτ2. closed_solver.
      + repeat econstructor; fold ga_pair.
        rewrite -val_subst_valid. apply context_weakening2. apply IHτ2. closed_solver.
        rewrite -val_subst_valid. apply context_weakening2. apply IHτ1. closed_solver.
      + constructor. constructor.
        apply App_typed with (τ1 := (τb.[TRec τb/])).
        2: constructor; constructor; by asimpl.
        simpl in *. apply IHn. admit.
      + admit.
  Admitted.


End guard_assert.
