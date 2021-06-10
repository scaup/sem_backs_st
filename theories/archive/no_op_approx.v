From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.prelude Require Import autosubst big_op_three.
From st.lam Require Import types lang typing tactics logrel.definitions logrel.generic.lift.
From st.lam.lib Require Import fixlam universe.embed_project guard_assert_approx universe.base.
From st.backtranslations.un_syn Require Import logrel.definitions logrel.un_le_syn.fundamental.
From st.backtranslations.sem_syn Require Import expl_idx.

Section guard_assert_no_op.

  Context `{Σ : !gFunctors}.

  Notation expl_idx n P := (@bi_entails (uPredI (iResUR Σ)) (▷^n False)%I P).

  Context `{irisG_inst : !irisG lam_lang Σ}.

  Context (s : stuckness).

  Notation valrel_typed := (valrel_typed s).
  Notation exprel_typed := (exprel_typed s).

  Local Notation "( x ; y )" := (existT x y) (at level 0, format "( x ;  '/  ' y )").

  Require Import FunInd Recdef.
  From Coq.Wellfounded Require Import Lexicographic_Product Union.
  From Coq.Relations Require Import Relation_Operators.
  From Coq.Program Require Import Wf.

  Function ga_val_eval (nτ : { n : nat & type}) (act : action) (v : val) {wf (lexprod nat (fun _ => type) lt (fun _ => lt_type)) nτ } : val :=
    match nτ with
    | (n;τ) =>
      match n with
      | O => v
      | S x =>
        match τ with
        | TUnit => v
        | TBool => v
        | TInt => v
        | TProd τ1 τ2 =>
          match v with
          | PairV v1 v2 => PairV (ga_val_eval (n;τ1) act v1) (ga_val_eval (n;τ2) act v2)
          | _ => v
          end
        | TSum τ1 τ2 => ()%Vₙₒ
        | TArrow τ1 τ2 => LamV ((ga_pair (n;τ2) act).{ren (+2)} (v.{ren (+1)}
                                            ((ga_pair (n;τ1) (opp_action act)).{ren (+2)} %0)))%Eₙₒ
        | TRec τb =>
          match v with
          | FoldV w => FoldV (ga_val_eval (x;τb.[TRec τb/]) act w)
          | _ => ()%Vₙₒ
          end
        | TVar X => ()%Vₙₒ
        end
      end
    end.

  1-3:by (intros; apply right_lex; simplify_eq; constructor) || (by intros; apply left_lex ; lia).
  apply wf_lexprod. apply lt_wf. intros _. intro τ. apply Acc_intro. induction τ; try by intros τ' abs; inversion abs.
  Defined.

  Instance val_inhabited : Inhabited val := populate ()%Vₙₒ.

  Lemma ga_termination (n : nat) (τ : type) (pCnτ : Closed_n 0 τ) :
    ∀ (act : action) (v v' : val)
      (H : expl_idx n (valrel_typed τ v v')), rtc lam_step (ga_pair (n;τ) act v') (ga_val_eval (n;τ) act v').
  Proof.
    generalize dependent τ.
    induction n.
    - intros τ pCτ act v v' H0vv'. rewrite ga_pair_equation ga_val_eval_equation.
      apply rtc_once. apply head_prim_step. econstructor. by rewrite to_of_val.
    - intros τ pCτ act v v' HSnvv'.
      induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τb IHτb | X ];
        rewrite ga_pair_equation ga_val_eval_equation.
      + (* TUnit *) setoid_rewrite valrel_typed_TUnit_unfold in HSnvv'. setoid_rewrite expl_idx_and in HSnvv'. setoid_rewrite expl_idx_S_n_pure in HSnvv'.
        destruct HSnvv' as [-> ->]. destruct act.
        * admit.
        * admit.
      + (* TBool *) setoid_rewrite valrel_typed_TBool_unfold in HSnvv'. setoid_rewrite expl_idx_S_n_exists in HSnvv'. destruct HSnvv' as [b HSnvv'].
        setoid_rewrite expl_idx_and in HSnvv'. setoid_rewrite expl_idx_S_n_pure in HSnvv'. destruct HSnvv' as [-> ->].
        destruct act.
        * admit.
        * admit.
      + (* TInt *)
        admit.
      + (* TProd *) setoid_rewrite valrel_typed_TProd_unfold in HSnvv'.
        do 4 setoid_rewrite expl_idx_S_n_exists in HSnvv'.
        setoid_rewrite expl_idx_and in HSnvv'.
        do 2 setoid_rewrite expl_idx_sep in HSnvv'.
        setoid_rewrite expl_idx_S_n_pure in HSnvv'.
        destruct HSnvv' as (v1 & v2 & v1' & v2' & -> & -> & HSnv1v1' & HSnv2v2').
        admit.
      + (* TSum *) admit.
      + (* TArrow *)
        admit.
      + (* TRec *) setoid_rewrite valrel_typed_TRec_unfold in HSnvv'.
        do 2 setoid_rewrite expl_idx_S_n_exists in HSnvv'.
        do 2 setoid_rewrite expl_idx_and in HSnvv'.
        setoid_rewrite expl_idx_S_n_pure in HSnvv'.
        setoid_rewrite expl_idx_S_n in HSnvv'.
        destruct HSnvv' as (w & w' & -> & -> & Hnww').
        (* step *)
        apply rtc_l with (y := (Fold (ga_pair (n;τb.[TRec τb/]) act (Unfold (Fold w'))))%Eₙₒ).
        { assert ((Fold (ga_pair (n;τb.[TRec τb/]) act (Unfold (Fold w')))) =
                  (Fold (ga_pair (n;τb.[TRec τb/]) act (Unfold (Var 0)))).[Fold w'/]) as ->. admit.
          apply head_prim_step. eapply App_Lam_head_step. change (Fold w') with (of_val $ FoldV w'). by rewrite to_of_val.
        }
        (* get rid of context *)
        apply (rtc_lam_step_ctx (fill [FoldCtx])). fold (of_val).
        (* step *)
        apply rtc_l with (y := (ga_pair (n; τb.[TRec τb/]) act w')).
        { apply (lam_step_ctx (fill [AppRCtx _])). apply head_prim_step. econstructor. by rewrite to_of_val.
        }
        eapply IHn; eauto. admit.
      + (* TVar *) exfalso. admit.
  Admitted.

