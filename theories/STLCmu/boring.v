(* STLCmu and STLCmuVS are the same thing;
   this file encodes this truth by a bunch of trivial mappings and lemmas *)

(* trivial embedding from STLCmu into STLCmuVS  *)
(* -------------------------------------------  *)

From st.STLCmu Require Import lang typing.
From st.STLCmuVS Require Import lang typing.
From st.prelude Require Import lang_base.

Reserved Notation "[[ e ]]" (at level 4, e at next level).
Fixpoint embd_expr (e : STLCmu.lang.expr) : STLCmuVS.lang.expr :=
  match e with
  | STLCmu.lang.Var x => Var x
  | STLCmu.lang.LetIn e1 e2 => LetIn [[e1]] [[e2]]
  | STLCmu.lang.Lam e => Lam [[e]]
  | STLCmu.lang.App e1 e2 => App [[e1]] [[e2]]
  | STLCmu.lang.Lit l => match l with
                       | LitInt n => n
                       | LitBool b => b
                       | LitUnit => ()%Eₙₒ
                       end
  | STLCmu.lang.BinOp op e1 e2 => BinOp op [[e1]] [[e2]]
  | STLCmu.lang.If e0 e1 e2 => If [[e0]] [[e1]] [[e2]]
  | STLCmu.lang.Seq e1 e2 => Seq [[e1]] [[e2]]
  | STLCmu.lang.Pair e1 e2 => Pair [[e1]] [[e2]]
  | STLCmu.lang.Fst e => Fst [[e]]
  | STLCmu.lang.Snd e => Snd [[e]]
  | STLCmu.lang.InjL e => InjL [[e]]
  | STLCmu.lang.InjR e => InjR [[e]]
  | STLCmu.lang.Case e0 e1 e2 => Case [[e0]] [[e1]] [[e2]]
  | STLCmu.lang.Fold e => Fold [[e]]
  | STLCmu.lang.Unfold e => Unfold [[e]]
  end
where "[[ e ]]" := (embd_expr e).

Lemma embd_expr_ren e :
  forall k l, [[ e.[upn l (ren (+k))] ]] = [[e]].[upn l (ren (+k))].
Proof.
  induction e; intros k m; asimpl.
  - do 2 rewrite (iter_up m x (ren (+k))).
    destruct (lt_dec x m); by asimpl.
  - erewrite IHe0. by erewrite IHe.
  - by erewrite IHe.
  - erewrite IHe1. by erewrite IHe2.
  - by destruct l.
  - erewrite IHe1. by erewrite IHe2.
  - erewrite IHe1. erewrite IHe2. by erewrite IHe3.
  - erewrite IHe1. by erewrite IHe2.
  - erewrite IHe1. by erewrite IHe2.
  - by erewrite IHe.
  - by erewrite IHe.
  - by erewrite IHe.
  - by erewrite IHe.
  - erewrite IHe. erewrite IHe0. by erewrite IHe1.
  - by erewrite IHe.
  - by erewrite IHe.
Qed.

Lemma comm_embd_expr_subst_gen e e' : ∀ n, [[e.[upn n (e' .: ids)] ]] = [[e]].[upn n ([[e']] .: ids)].
Proof.
  induction e; intros n; asimpl.
  - rewrite (iter_up n x (e' .: ids)) (iter_up n x ([[e']] .: ids)).
    destruct (lt_dec x n).
      + by asimpl.
      + destruct (decide (x - n = 0)); asimpl. rewrite e. asimpl.
        cut ([[ e'.[upn 0 (ren (+n))] ]] = ([[ e' ]]).[upn 0 (ren (+n))]).
        by asimpl. by rewrite embd_expr_ren.
        destruct (x - n). exfalso; lia. by asimpl.
  - erewrite IHe. by erewrite IHe0.
  - by erewrite IHe.
  - erewrite IHe1. by erewrite IHe2.
  - by destruct l.
  - erewrite IHe1. by erewrite IHe2.
  - erewrite IHe1. erewrite IHe2. by erewrite IHe3.
  - erewrite IHe1. by erewrite IHe2.
  - erewrite IHe1. by erewrite IHe2.
  - by erewrite IHe.
  - by erewrite IHe.
  - by erewrite IHe.
  - by erewrite IHe.
  - erewrite IHe. erewrite IHe0. by erewrite IHe1.
  - by erewrite IHe.
  - by erewrite IHe.
Qed.

Lemma comm_embd_expr_subst e e' : [[e.[e'/]]] = [[e]].[[[e']]/].
Proof.
  cut ([[e.[upn 0 (e' .: ids)] ]] = ([[e]]).[upn 0 ([[e']] .: ids)]); [by asimpl|].
  apply comm_embd_expr_subst_gen.
Qed.

Fixpoint embd_val (v : STLCmu.lang.val) : STLCmuVS.lang.val :=
  match v with
  | STLCmu.lang.LamV e => LamV (embd_expr e)
  | STLCmu.lang.LitV v => LitV v
  | STLCmu.lang.PairV v1 v2 => PairV (embd_val v1) (embd_val v2)
  | STLCmu.lang.InjLV v => InjLV (embd_val v)
  | STLCmu.lang.InjRV v => InjRV (embd_val v)
  | STLCmu.lang.FoldV v => FoldV (embd_val v)
  end.

Lemma to_val_embd_expr e : to_val (embd_expr e) = (STLCmu.lang.to_val e) ≫= (fun v => Some (embd_val v)).
Proof.
  induction e; simplify_option_eq; try done.
  - by destruct l.
  - simpl. rewrite IHe1 IHe2. simplify_option_eq.
    destruct (STLCmu.lang.to_val e1) eqn:eq1.
    + simplify_option_eq. destruct (STLCmu.lang.to_val e2) eqn:eq2; by simplify_option_eq.
    + by simplify_option_eq.
  - rewrite IHe. simplify_option_eq.
    destruct (STLCmu.lang.to_val e) eqn:eq; by simplify_option_eq.
  - rewrite IHe. simplify_option_eq.
    destruct (STLCmu.lang.to_val e) eqn:eq; by simplify_option_eq.
  - rewrite IHe. simplify_option_eq.
    destruct (STLCmu.lang.to_val e) eqn:eq; by simplify_option_eq.
Qed.

Lemma of_val_embd_expr v : of_val (embd_val v) = embd_expr (STLCmu.lang.of_val v).
Proof.
  induction v; simpl; try by rewrite IHv. done. by destruct v. by rewrite IHv1 IHv2. Qed.

Lemma embd_expr_typed Γ (e : STLCmu.lang.expr) τ (de : STLCmu.typing.typed Γ e τ) :
  STLCmuVS.typing.typed Γ (embd_expr e) τ.
Proof. induction de; try by repeat econstructor. Qed.

From st.STLCmu Require Import contexts.
From st.STLCmuVS Require Import contexts.

Definition embd_ctx_item (Ci : STLCmu.contexts.ctx_item) : STLCmuVS.contexts.ctx_item :=
  match Ci with
  | STLCmu.contexts.CTX_Lam => CTX_Lam
  | STLCmu.contexts.CTX_AppL e2 => CTX_AppL [[e2]]
  | STLCmu.contexts.CTX_AppR e1 => CTX_AppR [[e1]]
  | STLCmu.contexts.CTX_LetInL e2 => CTX_LetInL [[e2]]
  | STLCmu.contexts.CTX_LetInR e1 => CTX_LetInR [[e1]]
  | STLCmu.contexts.CTX_PairL e2 => CTX_PairL [[e2]]
  | STLCmu.contexts.CTX_PairR e1 => CTX_PairR [[e1]]
  | STLCmu.contexts.CTX_Fst => CTX_Fst
  | STLCmu.contexts.CTX_Snd => CTX_Snd
  | STLCmu.contexts.CTX_InjL => CTX_InjL
  | STLCmu.contexts.CTX_InjR => CTX_InjR
  | STLCmu.contexts.CTX_CaseL e1 e2 => CTX_CaseL [[e1]] [[e2]]
  | STLCmu.contexts.CTX_CaseM e0 e2 => CTX_CaseM [[e0]] [[e2]]
  | STLCmu.contexts.CTX_CaseR e0 e1 => CTX_CaseR [[e0]] [[e1]]
  | STLCmu.contexts.CTX_BinOpL op e2 => CTX_BinOpL op [[e2]]
  | STLCmu.contexts.CTX_BinOpR op e1 => CTX_BinOpR op [[e1]]
  | STLCmu.contexts.CTX_IfL e1 e2 => CTX_IfL [[e1]] [[e2]]
  | STLCmu.contexts.CTX_IfM e0 e2 => CTX_IfM [[e0]] [[e2]]
  | STLCmu.contexts.CTX_IfR e0 e1 => CTX_IfR [[e0]] [[e1]]
  | STLCmu.contexts.CTX_Fold => CTX_Fold
  | STLCmu.contexts.CTX_Unfold => CTX_Unfold
  end.

Definition embd_ctx (C : STLCmu.contexts.ctx) : STLCmuVS.contexts.ctx :=
  fmap embd_ctx_item C.

Lemma comm_embd_fill_ctx_item Ci e :
  STLCmuVS.contexts.fill_ctx_item (embd_ctx_item Ci) (embd_expr e) =
  embd_expr (STLCmu.contexts.fill_ctx_item Ci e).
Proof. destruct Ci; by simpl. Qed.

Lemma comm_embd_fill_ctx C e :
  STLCmuVS.contexts.fill_ctx (embd_ctx C) (embd_expr e) =
  embd_expr (STLCmu.contexts.fill_ctx C e).
Proof. induction C; simpl; try done. rewrite IHC. erewrite comm_embd_fill_ctx_item; eauto. Qed.

From st.STLCmu Require Import reducibility.
From st.STLCmuVS Require Import reducibility.

Lemma embd_expr_Reducible (e : STLCmu.lang.expr) (de : STLCmu.reducibility.Reducible e) :
  STLCmuVS.reducibility.Reducible (embd_expr e).
Proof.
  induction de; intros; simpl; try by econstructor.
  - eapply LetIn_D_Red. by rewrite to_val_embd_expr H.
  - eapply App_R_Red; auto. by rewrite to_val_embd_expr H.
  - eapply App_D_Red; auto. by rewrite to_val_embd_expr H.
  - eapply BinOp_R_Red; auto. by rewrite to_val_embd_expr H.
  - eapply Pair_R_Red; auto. by rewrite to_val_embd_expr H.
  - eapply Fst_D_Red; auto. by rewrite to_val_embd_expr H. by rewrite to_val_embd_expr H0.
  - eapply Snd_D_Red; auto. by rewrite to_val_embd_expr H. by rewrite to_val_embd_expr H0.
  - eapply Case_D_InjL_Red; auto. by rewrite to_val_embd_expr H.
  - eapply Case_D_InjR_Red; auto. by rewrite to_val_embd_expr H.
  - eapply Unfold_D_Red; auto. by rewrite to_val_embd_expr H.
Qed.

Lemma embd_expr_head_step_help (e : STLCmu.lang.expr) (e' : STLCmu.lang.expr) :
  STLCmu_head_step e e' → STLCmuVS_head_step (embd_expr e) (embd_expr e').
Proof.
  intro Hstep. destruct Hstep; simpl; try by econstructor.
  - rewrite comm_embd_expr_subst. econstructor. rewrite to_val_embd_expr H. by simplify_option_eq.
  - rewrite comm_embd_expr_subst. econstructor. rewrite to_val_embd_expr H. by simplify_option_eq.
  - rewrite -(STLCmu.lang.of_to_val _ _ H) -(STLCmu.lang.of_to_val _ _ H0). rewrite -!of_val_embd_expr /=.
    replace (STLCmuVS.lang.of_val (embd_val (STLCmu.lang.bin_op_eval op z1 z2))) with
        (of_val (bin_op_eval op z1 z2)) by by destruct op.
    by econstructor.
  - rewrite -(STLCmu.lang.of_to_val _ _ H) /=. by econstructor.
  - econstructor. by rewrite to_val_embd_expr H /=. by rewrite to_val_embd_expr H0 /=.
  - econstructor. by rewrite to_val_embd_expr H /=. by rewrite to_val_embd_expr H0 /=.
  - rewrite -(STLCmu.lang.of_to_val _ _ H) /= -of_val_embd_expr comm_embd_expr_subst of_val_embd_expr.
    econstructor. by rewrite to_val_embd_expr STLCmu.lang.to_of_val /=.
  - rewrite -(STLCmu.lang.of_to_val _ _ H) /= -of_val_embd_expr comm_embd_expr_subst of_val_embd_expr.
    econstructor. by rewrite to_val_embd_expr STLCmu.lang.to_of_val /=.
  - econstructor. by rewrite to_val_embd_expr H /=.
Qed.

Definition embd_ectx_item (Ki : STLCmu.lang.ectx_item) : STLCmuVS.lang.ectx_item :=
  match Ki with
  | STLCmu.lang.LetInCtx e2 => LetInCtx [[e2]]
  | STLCmu.lang.AppLCtx e2 => AppLCtx [[e2]]
  | STLCmu.lang.AppRCtx v1 => AppRCtx (embd_val v1)
  | STLCmu.lang.PairLCtx e2 => PairLCtx [[e2]]
  | STLCmu.lang.PairRCtx v1 => PairRCtx (embd_val v1)
  | STLCmu.lang.FstCtx => FstCtx
  | STLCmu.lang.SndCtx => SndCtx
  | STLCmu.lang.InjLCtx => InjLCtx
  | STLCmu.lang.InjRCtx => InjRCtx
  | STLCmu.lang.CaseCtx e1 e2 => CaseCtx [[e1]] [[e2]]
  | STLCmu.lang.IfCtx e2 e3 => IfCtx [[e2]] [[e3]]
  | STLCmu.lang.BinOpLCtx op e2 => BinOpLCtx op [[e2]]
  | STLCmu.lang.BinOpRCtx op v1 => BinOpRCtx op (embd_val v1)
  | STLCmu.lang.SeqCtx e2 => SeqCtx [[e2]]
  | STLCmu.lang.FoldCtx => FoldCtx
  | STLCmu.lang.UnfoldCtx => UnfoldCtx
  end.

Definition embd_ectx (K : list STLCmu.lang.ectx_item) : (list STLCmuVS.lang.ectx_item) :=
  fmap embd_ectx_item K.

Lemma comm_embd_fill_ectx_item Ki e :
  STLCmuVS.lang.fill_item (embd_ectx_item Ki) (embd_expr e) =
  embd_expr (STLCmu.lang.fill_item Ki e).
Proof. destruct Ki; simpl; try done; by rewrite of_val_embd_expr. Qed.

Lemma comm_embd_fill_ectx K e :
  fill (embd_ectx K) (embd_expr e) = embd_expr (fill K e).
Proof.
  induction K as [|Ki K IHK] using rev_ind; simpl; try done.
  replace (embd_ectx (K ++ [Ki])) with (embd_ectx K ++ [embd_ectx_item Ki]) by (rewrite /embd_ectx fmap_app; done).
  by rewrite !fill_app IHK /= comm_embd_fill_ectx_item.
Qed.

Lemma embd_expr_step_help (e : STLCmu.lang.expr) (e' : STLCmu.lang.expr) :
  STLCmu_step e e' → STLCmuVS_step (embd_expr e) (embd_expr e').
Proof.
  intro Hstep. destruct Hstep. subst. simpl.
  rewrite -!comm_embd_fill_ectx.
  apply STLCmuVS_step_ctx. apply (@ectx_lang_ctx STLCmuVS_ectx_lang).
  by apply head_prim_step, embd_expr_head_step_help.
Qed.

Lemma embd_expr_step (e : STLCmu.lang.expr) :
  ∀ (e' : STLCmu.lang.expr), STLCmu_step e e' → STLCmuVS_step (embd_expr e) (embd_expr e').
Proof.
  intros e' Hstep.
  cut (Reducible [[e]]).
  { intro red. pose proof (iffRL (Reducible_valid _) red).
    pose proof (iffRL (STLCmuVS_prim_red _) H).
    destruct H0 as [e'' Hstep'].
    by apply embd_expr_step_help.
  }
  apply embd_expr_Reducible.
  apply STLCmu.reducibility.Reducible_valid.
  apply STLCmu_prim_red. by exists e'.
Qed.

Lemma embd_expr_halts (e : STLCmu.lang.expr) :
  STLCmu_halts e → STLCmuVS_halts (embd_expr e).
Proof.
  intros halts. destruct halts as [v Hrtc].
  exists (embd_val v). rewrite of_val_embd_expr.
  eapply rtc_congruence; eauto. apply embd_expr_step.
Qed.

(* trivial projection from STLCmuVS into STLCmu  *)
(* --------------------------------------------  *)

From st.STLCmuVS Require Import lang.
From st.STLCmu Require Import lang.
From st.prelude Require Import lang_base.

Reserved Notation "<< e >>" (at level 4, e at next level).
Fixpoint proj_expr (e : STLCmuVS.lang.expr) : STLCmu.lang.expr :=
  match e with
  | STLCmuVS.lang.Var x => Var x
  | STLCmuVS.lang.LetIn e1 e2 => LetIn <<e1>> <<e2>>
  | STLCmuVS.lang.Lam e => Lam <<e>>
  | STLCmuVS.lang.App e1 e2 => App <<e1>> <<e2>>
  | STLCmuVS.lang.Lit l => match l with
                       | LitInt n => Lit (LitInt n)
                       | LitBool b => Lit (LitBool b)
                       | LitUnit => Lit LitUnit
                       end
  | STLCmuVS.lang.BinOp op e1 e2 => BinOp op <<e1>> <<e2>>
  | STLCmuVS.lang.If e0 e1 e2 => If <<e0>> <<e1>> <<e2>>
  | STLCmuVS.lang.Seq e1 e2 => Seq <<e1>> <<e2>>
  | STLCmuVS.lang.Pair e1 e2 => Pair <<e1>> <<e2>>
  | STLCmuVS.lang.Fst e => Fst <<e>>
  | STLCmuVS.lang.Snd e => Snd <<e>>
  | STLCmuVS.lang.InjL e => InjL <<e>>
  | STLCmuVS.lang.InjR e => InjR <<e>>
  | STLCmuVS.lang.Case e0 e1 e2 => Case <<e0>> <<e1>> <<e2>>
  | STLCmuVS.lang.Fold e => Fold <<e>>
  | STLCmuVS.lang.Unfold e => Unfold <<e>>
  | STLCmuVS.lang.VirtStep e => (Seq (Lit LitUnit) (Lit LitUnit)) (* just a dummy value *)
  end
where "<< e >>" := (proj_expr e).

Lemma retraction (e : STLCmu.lang.expr) : proj_expr (embd_expr e) = e.
Proof.
  induction e; simpl; try done; try destruct (_ : base_lit); (repeat f_equiv; auto).
Qed.

From st.STLCmuVS Require Import contexts.
From st.STLCmu Require Import contexts.

Definition proj_ctx_item (Ci : STLCmuVS.contexts.ctx_item) : STLCmu.contexts.ctx_item :=
  match Ci with
  | STLCmuVS.contexts.CTX_Lam => CTX_Lam
  | STLCmuVS.contexts.CTX_AppL e2 => CTX_AppL <<e2>>
  | STLCmuVS.contexts.CTX_AppR e1 => CTX_AppR <<e1>>
  | STLCmuVS.contexts.CTX_LetInL e2 => CTX_LetInL <<e2>>
  | STLCmuVS.contexts.CTX_LetInR e1 => CTX_LetInR <<e1>>
  | STLCmuVS.contexts.CTX_PairL e2 => CTX_PairL <<e2>>
  | STLCmuVS.contexts.CTX_PairR e1 => CTX_PairR <<e1>>
  | STLCmuVS.contexts.CTX_Fst => CTX_Fst
  | STLCmuVS.contexts.CTX_Snd => CTX_Snd
  | STLCmuVS.contexts.CTX_InjL => CTX_InjL
  | STLCmuVS.contexts.CTX_InjR => CTX_InjR
  | STLCmuVS.contexts.CTX_CaseL e1 e2 => CTX_CaseL <<e1>> <<e2>>
  | STLCmuVS.contexts.CTX_CaseM e0 e2 => CTX_CaseM <<e0>> <<e2>>
  | STLCmuVS.contexts.CTX_CaseR e0 e1 => CTX_CaseR <<e0>> <<e1>>
  | STLCmuVS.contexts.CTX_BinOpL op e2 => CTX_BinOpL op <<e2>>
  | STLCmuVS.contexts.CTX_BinOpR op e1 => CTX_BinOpR op <<e1>>
  | STLCmuVS.contexts.CTX_IfL e1 e2 => CTX_IfL <<e1>> <<e2>>
  | STLCmuVS.contexts.CTX_IfM e0 e2 => CTX_IfM <<e0>> <<e2>>
  | STLCmuVS.contexts.CTX_IfR e0 e1 => CTX_IfR <<e0>> <<e1>>
  | STLCmuVS.contexts.CTX_Fold => CTX_Fold
  | STLCmuVS.contexts.CTX_Unfold => CTX_Unfold
  | STLCmuVS.contexts.CTX_VirtStep => CTX_Lam (* just a dummy value *)
  end.

Definition proj_ctx (C : STLCmuVS.contexts.ctx) : STLCmu.contexts.ctx :=
  fmap proj_ctx_item C.

From st.STLCmuVS Require Import lang typing reducibility.
From st.STLCmu Require Import types lang typing.
From st.prelude Require Import lang_base.

Lemma proj_expr_typed Γ (e : STLCmuVS.lang.expr) τ (de : STLCmuVS.typing.typed Γ e τ) :
  STLCmu.typing.typed Γ (proj_expr e) τ.
Proof. induction de; try by repeat econstructor. Qed.

Lemma proj_expr_ren e :
  forall k l, << e.[upn l (ren (+k))] >> = <<e>>.[upn l (ren (+k))].
Proof.
  induction e; intros k m; asimpl.
  - do 2 rewrite (iter_up m x (ren (+k))).
    destruct (lt_dec x m); by asimpl.
  - erewrite IHe0. by erewrite IHe.
  - by erewrite IHe.
  - erewrite IHe1. by erewrite IHe2.
  - by destruct l.
  - erewrite IHe1. by erewrite IHe2.
  - erewrite IHe1. erewrite IHe2. by erewrite IHe3.
  - erewrite IHe1. by erewrite IHe2.
  - erewrite IHe1. by erewrite IHe2.
  - by erewrite IHe.
  - by erewrite IHe.
  - by erewrite IHe.
  - by erewrite IHe.
  - erewrite IHe. erewrite IHe0. by erewrite IHe1.
  - by erewrite IHe.
  - by erewrite IHe.
  - done.
Qed.

Lemma comm_proj_expr_subst_gen e e' : ∀ n, <<e.[upn n (e' .: ids)] >> = <<e>>.[upn n (<<e'>> .: ids)].
Proof.
  induction e; intros n; asimpl.
  - rewrite (iter_up n x (e' .: ids)) (iter_up n x (<<e'>> .: ids)).
    destruct (lt_dec x n).
      + by asimpl.
      + destruct (decide (x - n = 0)); asimpl. rewrite e. asimpl.
        cut (<< e'.[upn 0 (ren (+n))] >> = (<< e' >>).[upn 0 (ren (+n))]).
        by asimpl. by rewrite proj_expr_ren.
        destruct (x - n). exfalso; lia. by asimpl.
  - erewrite IHe. by erewrite IHe0.
  - by erewrite IHe.
  - erewrite IHe1. by erewrite IHe2.
  - by destruct l.
  - erewrite IHe1. by erewrite IHe2.
  - erewrite IHe1. erewrite IHe2. by erewrite IHe3.
  - erewrite IHe1. by erewrite IHe2.
  - erewrite IHe1. by erewrite IHe2.
  - by erewrite IHe.
  - by erewrite IHe.
  - by erewrite IHe.
  - by erewrite IHe.
  - erewrite IHe. erewrite IHe0. by erewrite IHe1.
  - by erewrite IHe.
  - by erewrite IHe.
  - done.
Qed.

Lemma comm_proj_expr_subst e e' : <<e.[e'/]>> = <<e>>.[<<e'>>/].
Proof.
  cut (<<e.[upn 0 (e' .: ids)] >> = (<<e>>).[upn 0 (<<e'>> .: ids)]); [by asimpl|].
  apply comm_proj_expr_subst_gen.
Qed.

Fixpoint proj_val (v : STLCmuVS.lang.val) : STLCmu.lang.val :=
  match v with
  | STLCmuVS.lang.LamV e => LamV (proj_expr e)
  | STLCmuVS.lang.LitV v => LitV v
  | STLCmuVS.lang.PairV v1 v2 => PairV (proj_val v1) (proj_val v2)
  | STLCmuVS.lang.InjLV v => InjLV (proj_val v)
  | STLCmuVS.lang.InjRV v => InjRV (proj_val v)
  | STLCmuVS.lang.FoldV v => FoldV (proj_val v)
  end.

Lemma to_val_proj_expr e : to_val (proj_expr e) = (STLCmuVS.lang.to_val e) ≫= (fun v => Some (proj_val v)).
Proof.
  induction e; simplify_option_eq; try done.
  - by destruct l.
  - simpl. rewrite IHe1 IHe2. simplify_option_eq.
    destruct (STLCmuVS.lang.to_val e1) eqn:eq1.
    + simplify_option_eq. destruct (STLCmuVS.lang.to_val e2) eqn:eq2; by simplify_option_eq.
    + by simplify_option_eq.
  - rewrite IHe. simplify_option_eq.
    destruct (STLCmuVS.lang.to_val e) eqn:eq; by simplify_option_eq.
  - rewrite IHe. simplify_option_eq.
    destruct (STLCmuVS.lang.to_val e) eqn:eq; by simplify_option_eq.
  - rewrite IHe. simplify_option_eq.
    destruct (STLCmuVS.lang.to_val e) eqn:eq; by simplify_option_eq.
Qed.

Lemma of_val_proj_expr v : of_val (proj_val v) = proj_expr (STLCmuVS.lang.of_val v).
Proof.
  induction v; simpl; try by rewrite IHv. done. by destruct v. by rewrite IHv1 IHv2. Qed.

Lemma proj_ctx_item_typed Γ τ Γ' τ'
      (Ci : STLCmuVS.contexts.ctx_item) (pCi : STLCmuVS.contexts.typed_ctx_item Ci Γ τ Γ' τ') :
  STLCmu.contexts.typed_ctx_item (proj_ctx_item Ci) Γ τ Γ' τ'.
Proof. induction pCi; repeat econstructor; by eapply proj_expr_typed. Qed.

Lemma proj_ctx_typed Γ τ Γ' τ'
      (C : STLCmuVS.contexts.ctx) (pC : STLCmuVS.contexts.typed_ctx C Γ τ Γ' τ') :
  STLCmu.contexts.typed_ctx (proj_ctx C) Γ τ Γ' τ'.
Proof. induction pC; repeat econstructor. by apply proj_ctx_item_typed. apply IHpC. Qed.

Lemma comm_proj_fill_ctx_item Ci Γ τ Γ' τ' (dCi : STLCmuVS.contexts.typed_ctx_item Ci Γ τ Γ' τ') e :
  STLCmu.contexts.fill_ctx_item (proj_ctx_item Ci) (proj_expr e) =
  proj_expr (STLCmuVS.contexts.fill_ctx_item Ci e).
Proof. destruct dCi; by simpl. Qed.

Lemma comm_proj_fill_ctx C Γ τ Γ' τ' (dC : STLCmuVS.contexts.typed_ctx C Γ τ Γ' τ') e :
  STLCmu.contexts.fill_ctx (proj_ctx C) (proj_expr e) =
  proj_expr (STLCmuVS.contexts.fill_ctx C e).
Proof. induction dC; simpl; try done. rewrite IHdC. erewrite comm_proj_fill_ctx_item; eauto. Qed.

From st.STLCmuVS Require Import reducibility.
From st.STLCmu Require Import reducibility.

Lemma proj_expr_Reducible (e : STLCmuVS.lang.expr) (de : STLCmuVS.reducibility.Reducible e) :
  STLCmu.reducibility.Reducible (proj_expr e).
Proof.
  induction de; intros; simpl; try by econstructor.
  - eapply LetIn_D_Red. by rewrite to_val_proj_expr H.
  - eapply App_R_Red; auto. by rewrite to_val_proj_expr H.
  - eapply App_D_Red; auto. by rewrite to_val_proj_expr H.
  - eapply BinOp_R_Red; auto. by rewrite to_val_proj_expr H.
  - eapply Pair_R_Red; auto. by rewrite to_val_proj_expr H.
  - eapply Fst_D_Red; auto. by rewrite to_val_proj_expr H. by rewrite to_val_proj_expr H0.
  - eapply Snd_D_Red; auto. by rewrite to_val_proj_expr H. by rewrite to_val_proj_expr H0.
  - eapply Case_D_InjL_Red; auto. by rewrite to_val_proj_expr H.
  - eapply Case_D_InjR_Red; auto. by rewrite to_val_proj_expr H.
  - eapply Unfold_D_Red; auto. by rewrite to_val_proj_expr H.
Qed.

Lemma proj_expr_head_step_help (e : STLCmuVS.lang.expr) Γ τ (de : STLCmuVS.typing.typed Γ e τ) (e' : STLCmuVS.lang.expr) :
  STLCmuVS_head_step e e' → STLCmu_head_step (proj_expr e) (proj_expr e').
Proof.
  intro Hstep. destruct Hstep; simpl; (try by econstructor); (try by inversion de).
  - rewrite comm_proj_expr_subst. econstructor. rewrite to_val_proj_expr H. by simplify_option_eq.
  - rewrite comm_proj_expr_subst. econstructor. rewrite to_val_proj_expr H. by simplify_option_eq.
  - rewrite -(STLCmuVS.lang.of_to_val _ _ H) -(STLCmuVS.lang.of_to_val _ _ H0). rewrite -!of_val_proj_expr /=.
    replace (STLCmu.lang.of_val (proj_val (STLCmuVS.lang.bin_op_eval op z1 z2))) with
        (of_val (bin_op_eval op z1 z2)) by by destruct op.
    by econstructor.
  - rewrite -(STLCmuVS.lang.of_to_val _ _ H) /=. by econstructor.
  - econstructor. by rewrite to_val_proj_expr H /=. by rewrite to_val_proj_expr H0 /=.
  - econstructor. by rewrite to_val_proj_expr H /=. by rewrite to_val_proj_expr H0 /=.
  - rewrite -(STLCmuVS.lang.of_to_val _ _ H) /= -of_val_proj_expr comm_proj_expr_subst of_val_proj_expr.
    econstructor. by rewrite to_val_proj_expr STLCmuVS.lang.to_of_val /=.
  - rewrite -(STLCmuVS.lang.of_to_val _ _ H) /= -of_val_proj_expr comm_proj_expr_subst of_val_proj_expr.
    econstructor. by rewrite to_val_proj_expr STLCmuVS.lang.to_of_val /=.
  - econstructor. by rewrite to_val_proj_expr H /=.
Qed.

Definition proj_ectx_item (Ki : STLCmuVS.lang.ectx_item) : STLCmu.lang.ectx_item :=
  match Ki with
  | STLCmuVS.lang.LetInCtx e2 => LetInCtx <<e2>>
  | STLCmuVS.lang.AppLCtx e2 => AppLCtx <<e2>>
  | STLCmuVS.lang.AppRCtx v1 => AppRCtx (proj_val v1)
  | STLCmuVS.lang.PairLCtx e2 => PairLCtx <<e2>>
  | STLCmuVS.lang.PairRCtx v1 => PairRCtx (proj_val v1)
  | STLCmuVS.lang.FstCtx => FstCtx
  | STLCmuVS.lang.SndCtx => SndCtx
  | STLCmuVS.lang.InjLCtx => InjLCtx
  | STLCmuVS.lang.InjRCtx => InjRCtx
  | STLCmuVS.lang.CaseCtx e1 e2 => CaseCtx <<e1>> <<e2>>
  | STLCmuVS.lang.IfCtx e2 e3 => IfCtx <<e2>> <<e3>>
  | STLCmuVS.lang.BinOpLCtx op e2 => BinOpLCtx op <<e2>>
  | STLCmuVS.lang.BinOpRCtx op v1 => BinOpRCtx op (proj_val v1)
  | STLCmuVS.lang.SeqCtx e2 => SeqCtx <<e2>>
  | STLCmuVS.lang.FoldCtx => FoldCtx
  | STLCmuVS.lang.UnfoldCtx => UnfoldCtx
  | STLCmuVS.lang.VirtStepCtx => UnfoldCtx
  end.

Definition proj_ectx (K : list STLCmuVS.lang.ectx_item) : (list STLCmu.lang.ectx_item) :=
  fmap proj_ectx_item K.

Lemma comm_proj_fill_ectx_item Ki (pKi : Ki ≠ VirtStepCtx) e :
  STLCmu.lang.fill_item (proj_ectx_item Ki) (proj_expr e) =
  proj_expr (STLCmuVS.lang.fill_item Ki e).
Proof. destruct Ki; simpl; try done; by rewrite of_val_proj_expr. Qed.

Lemma comm_proj_fill_ectx K (pK : Forall (fun Ki => Ki ≠ VirtStepCtx) K) e :
  fill (proj_ectx K) (proj_expr e) = proj_expr (fill K e).
Proof.
  revert pK.
  induction K as [|Ki K IHK] using rev_ind; simpl; try done. intro pK.
  destruct (iffLR (Forall_app _ _ _) pK) as [pK' pKi]. inversion_clear pKi.
  replace (proj_ectx (K ++ [Ki])) with (proj_ectx K ++ [proj_ectx_item Ki]) by (rewrite /proj_ectx fmap_app; done). specialize (IHK pK').
  rewrite !fill_app IHK /= comm_proj_fill_ectx_item; auto.
Qed.

Lemma blaa K : ∀ Γ e τ, STLCmuVS.typing.typed Γ (fill K e) τ → ∃ Γ' τ', STLCmuVS.typing.typed Γ' e τ'.
Proof.
  induction K as [|Ki K IHK] using rev_ind; intros; simpl in *.
  - by repeat eexists.
  - rewrite fill_app in H.
    destruct Ki; inversion H; subst; (try by inversion H0); by eapply IHK.
Qed.

Lemma blaa' K : ∀ Γ e τ, STLCmuVS.typing.typed Γ (fill K e) τ → Forall (λ Ki : lang.ectx_item, Ki ≠ VirtStepCtx) K.
Proof.
  induction K as [|Ki K IHK] using rev_ind; intros; simpl in *; try done.
  rewrite fill_app in H. apply Forall_app.
  destruct Ki; inversion H; subst; (try by inversion H0); (by split; [eapply IHK|auto]).
Qed.

Lemma proj_expr_step_help (e : STLCmuVS.lang.expr) Γ τ (de : STLCmuVS.typing.typed Γ e τ)
      (e' : STLCmuVS.lang.expr) :
  STLCmuVS_step e e' → STLCmu_step (proj_expr e) (proj_expr e').
Proof.
  intro Hstep. destruct Hstep. subst. simpl.
  rewrite -!comm_proj_fill_ectx.
  apply STLCmu_step_ctx. apply (@ectx_lang_ctx STLCmu_ectx_lang).
  eapply head_prim_step.
  destruct (blaa _ _ _ _ de) as (Γ' & τ' & de').
  by eapply proj_expr_head_step_help.
  eapply blaa', de.
  eapply blaa', de.
Qed.

Lemma proj_expr_step (e : STLCmuVS.lang.expr) Γ τ (de : STLCmuVS.typing.typed Γ e τ):
  ∀ (e' : STLCmuVS.lang.expr), STLCmuVS_step e e' → STLCmu_step (proj_expr e) (proj_expr e').
Proof.
  intros e' Hstep.
  cut (Reducible <<e>>).
  { intro red. pose proof (iffRL (Reducible_valid _) red).
    pose proof (iffRL (STLCmu_prim_red _) H).
    destruct H0 as [e'' Hstep'].
    by eapply proj_expr_step_help.
  }
  apply proj_expr_Reducible.
  apply STLCmuVS.reducibility.Reducible_valid.
  apply STLCmuVS_prim_red. by exists e'.
Qed.

Definition STLCmuVS_step_typed : relation STLCmuVS.lang.expr :=
  fun e e' => STLCmuVS_step e e' ∧ (∃ Γ τ, STLCmuVS.typing.typed Γ e τ ∧ STLCmuVS.typing.typed Γ e' τ).

Lemma rtc_STLCmuVS_step_typed (e e' : STLCmuVS.lang.expr) Γ τ (de : STLCmuVS.typing.typed Γ e τ) :
  rtc STLCmuVS_step e e' → rtc STLCmuVS_step_typed e e'.
Proof.
  intro rtc. revert Γ τ de. induction rtc.
  - constructor.
  - intros. eapply rtc_l. repeat split. apply H. exists Γ, τ.
    split; auto.
    eapply preservation; eauto. apply reducibility.Reducible_valid. apply STLCmuVS_prim_red. by eexists.
    eapply IHrtc.
    eapply preservation; eauto. apply reducibility.Reducible_valid. apply STLCmuVS_prim_red. by eexists.
Qed.

Lemma proj_expr_halts (e : STLCmuVS.lang.expr) Γ τ (de : STLCmuVS.typing.typed Γ e τ) :
  STLCmuVS_halts e → STLCmu_halts (proj_expr e).
Proof.
  intros halts. destruct halts as [v Hrtc].
  exists (proj_val v). rewrite of_val_proj_expr.
  assert (rtc STLCmuVS_step_typed e v).
  { eapply rtc_subrel. eauto.
    eapply rtc_STLCmuVS_step_typed; eauto.
  }
  eapply rtc_congruence; [|apply H].
  intros e' e'' (Hstep & (Γ' & τ' & [de' de''])).
  eapply proj_expr_step; eauto.
Qed.

Lemma inverse (e : STLCmuVS.lang.expr) Γ τ (de : STLCmuVS.typing.typed Γ e τ) :
  embd_expr (proj_expr e) = e.
Proof. induction de; simpl; (try done); (try by rewrite IHde1 IHde2); (try by rewrite IHde1 IHde2 IHde3); (try by rewrite IHde). Qed.

Lemma proj_expr_halts' (e : STLCmuVS.lang.expr) Γ τ (de : STLCmuVS.typing.typed Γ e τ) :
  STLCmu_halts (proj_expr e) → STLCmuVS_halts e.
Proof.
  intros halts. pose proof (embd_expr_halts _ halts) as halts'.
  erewrite inverse in halts'; eauto.
Qed.

Lemma proj_expr_halts_iff (e : STLCmuVS.lang.expr) Γ τ (de : STLCmuVS.typing.typed Γ e τ) :
  STLCmuVS_halts e <-> STLCmu_halts (proj_expr e).
Proof. split; [by eapply proj_expr_halts | by eapply proj_expr_halts']. Qed.

(* composing (STLCmu → STLCmuVS) with (STLCmuVS → STLCmuST) gives (STLCmu → STLCmuST) *)
(* ---------------------------------------------------------------------------------- *)

From st.embedding Require expressions contexts.
From st.end_to_end Require embedding_STLCmu_STLCmuST.

Lemma comp_embeddings (e : STLCmu.lang.expr) :
  embedding.expressions.embd_expr (embd_expr e) = embedding_STLCmu_STLCmuST.embd_expr e.
Proof. induction e; by simpl; repeat f_equiv; (try destruct (_ : base_lit)). Qed.
