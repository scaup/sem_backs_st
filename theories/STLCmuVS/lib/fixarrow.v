From st.STLCmuVS Require Import lang tactics typing.
From st.STLCmu Require Import types.

Local Open Scope expr_no_st_scope.
Local Open Scope types_no_st_scope.

Definition FixArrow (f : expr) : expr :=
  Unfold (Fold (Lam ((f.[ren (+1)]) (Lam ((Unfold (Var 1)) (Var 1) (Var 0))))))
    (Fold (Lam (f.[ren (+1)] (Lam ((Unfold (Var 1)) (Var 1) (Var 0)))))).

Lemma FixArrow_subst e σ : (FixArrow e).[σ] = FixArrow e.[σ].
Proof. rewrite /FixArrow. by asimpl. Qed.

Lemma help τ1 τ2 : (TRec (TVar 0 ⟶ τ1.[ren (+1)] ⟶ τ2.[ren (+1)]) ⟶ τ1 ⟶ τ2)%Tₙₒ = (TVar 0 ⟶ τ1.[ren (+1)] ⟶ τ2.[ren (+1)]).[TRec (TVar 0 ⟶ τ1.[ren (+1)] ⟶ τ2.[ren (+1)])%Tₙₒ/].
Proof. by asimpl. Qed.

Lemma FixArrow_typed Γ τ1 τ2 f : (Γ ⊢ₙₒ f : TArrow (TArrow τ1 τ2) (TArrow τ1 τ2))
  -> (Γ ⊢ₙₒ FixArrow f : TArrow τ1 τ2).
Proof.
  intro df. apply App_typed with (τ1 := (TRec (TVar 0 ⟶ τ1.[ren (+1)] ⟶ τ2.[ren (+1)]))%Tₙₒ).
  rewrite help. apply Unfold_typed. apply Fold_typed. apply Lam_typed. apply App_typed with (τ1 := TArrow τ1 τ2). asimpl.
  change ([ TRec (TVar 0 ⟶ τ1.[ren (+1)] ⟶ τ2.[ren (+1)]) ] ++ Γ ⊢ₙₒ f.[ren (+ length [ TRec (TVar 0 ⟶ τ1.[ren (+1)] ⟶ τ2.[ren (+1)]) ])] : ((τ1 ⟶ τ2) ⟶ τ1 ⟶ τ2)%Tₙₒ). by apply context_weakening.
  asimpl. apply Lam_typed. eapply App_typed. econstructor. erewrite help. apply Unfold_typed. by constructor. by constructor. by constructor.
  apply Fold_typed. apply Lam_typed. apply App_typed with (τ1 := TArrow τ1 τ2). asimpl.
  change ([ TRec (TVar 0 ⟶ τ1.[ren (+1)] ⟶ τ2.[ren (+1)]) ] ++ Γ ⊢ₙₒ f.[ren (+ length [ TRec (TVar 0 ⟶ τ1.[ren (+1)] ⟶ τ2.[ren (+1)]) ])] : ((τ1 ⟶ τ2) ⟶ τ1 ⟶ τ2)%Tₙₒ). by apply context_weakening.
  asimpl. apply Lam_typed. eapply App_typed. econstructor. erewrite help. apply Unfold_typed. by constructor. by constructor. by constructor.
Qed.

Lemma FixArrow_eval f : nsteps STLCmuVS_step 2 (FixArrow f) (f (Lam ((FixArrow f).[ren (+1)] %0)))%Eₙₒ.
Proof. do 2 (eapply nsteps_l; first auto_STLCmuVS_step; asimpl). by apply nsteps_O. Qed.

Definition Rec (e : {bind 2 of expr}) : val :=
  LamV ((FixArrow (Lam (Lam e))).[ren (+1)] %0)%Eₙₒ.

(* Definition Rec (e : {bind 2 of expr}) : expr := *)
(*   Lam ((FixArrow (Lam (Lam e.[upn 0 (ren (lookup_n (swap_list 1 1)))]))).[ren (+1)] %0)%Eₙₒ. *)

Lemma Rec_typed Γ e τ1 τ2 : (τ1 :: TArrow τ1 τ2 :: Γ ⊢ₙₒ e : τ2)
  -> (Γ ⊢ₙₒ Rec e : TArrow τ1 τ2).
Proof.
  constructor. apply App_typed with (τ1 := τ1). apply context_weakening1. apply FixArrow_typed. constructor. by constructor. by constructor.
  (* cut ([] ++ [τ1] ++ [TArrow τ1 τ2] ++ Γ ⊢ₙₒ e.[upn (length ([] : list type)) (ren (lookup_n (swap_list (length [τ1]) (length [TArrow τ1 τ2]))))] : τ2). by asimpl. *)
  (* apply context_swap_typed. by simpl. by constructor. *)
Qed.

Global Opaque FixArrow.


Lemma Rec_subst (e : {bind 2 of expr}) σ : (of_val $ Rec e).[σ] = of_val $ Rec (e.[ids 0 .: ids 1 .: σ >> ren (+2)]).
Proof.
  asimpl. rewrite !FixArrow_subst. by asimpl.
Qed.

Lemma App_Rec_nsteps e1 e2 v2 :
   to_val e2 = Some v2 →
   nsteps STLCmuVS_step 5 (App (Rec e1) e2) e1.[e2, (of_val $ Rec e1)/].
Proof.
  intros.
  eapply nsteps_l. auto_STLCmuVS_step. simplify_custom.
  change 4 with (2 + 2)%nat.
  eapply nsteps_trans. apply (nsteps_STLCmuVS_step_ctx (fill_item (AppLCtx _))). apply FixArrow_eval.
  rewrite FixArrow_subst. asimpl.
  eapply nsteps_l. auto_STLCmuVS_step. simplify_custom.
  rewrite FixArrow_subst. asimpl.
  eapply nsteps_l. auto_STLCmuVS_step. simplify_custom.
  rewrite FixArrow_subst. asimpl.
  rewrite (of_to_val _ _ H) /Rec.
  apply nsteps_O.
Qed.

Global Opaque Rec.

(* Lemma App_Rec_nsteps e1 e2 v2 : *)
(*    to_val e2 = Some v2 → *)
(*    nsteps STLCmuVS_step 5 (App (Rec e1) e2) e1.[(Rec e1), e2/]. *)
(* Proof. *)
(*   intros. *)
(*   eapply nsteps_l. auto_STLCmuVS_step. simplify_custom. *)
(*   change 4 with (2 + 2)%nat. *)
(*   eapply nsteps_trans. apply (nsteps_STLCmuVS_step_ctx (fill_item (AppLCtx _))). apply FixArrow_eval. *)
(*   rewrite FixArrow_subst. asimpl. *)
(*   eapply nsteps_l. auto_STLCmuVS_step. simplify_custom. *)
(*   rewrite FixArrow_subst. asimpl. *)
(*   eapply nsteps_l. auto_STLCmuVS_step. simplify_custom. *)
(*   rewrite FixArrow_subst. asimpl. *)

(* Lemma FixArrow_eval f : nsteps STLCmuVS_step 2 (FixArrow f) (f (Lam ((FixArrow f).[ren (+1)] %0)))%Eₙₒ. *)
(* Proof. do 2 (eapply nsteps_l; first auto_STLCmuVS_step; asimpl). by apply nsteps_O. Qed. *)



(* Definition FixLamBodyHelp (e : expr) := Lam ((Lam (e.[(%0 ())%Eₙₒ .: ren (+1)].[ren (+1)]))). *)

(* Definition FixLam (e : expr) := *)
(*   (Lam ((FixArrow (FixLamBodyHelp e)).[ren (+1)] %0) ())%Eₙₒ. *)

(* Lemma FixLam_eval e : nsteps STLCmuVS_step 5 (FixLam e) (e.[FixLam e/]). *)
(* Proof. *)
(*   eapply nsteps_l. apply head_prim_step. auto_head_step. *)
(*   cut (nsteps STLCmuVS_step 4 ((FixArrow (FixLamBodyHelp e)) ()) e.[FixLam e/])%Eₙₒ. asimpl. *)
(*   rewrite /FixArrow. by asimpl. *)
(*   assert (4 = (2 + 2)%nat) as ->. done. *)
(*   eapply nsteps_trans. *)
(*   eapply (nsteps_congruence (fill [AppLCtx ()%Eₙₒ])). intros. apply STLCmuVS_step_ctx. apply ectx_lang_ctx. apply H. *)
(*   apply FixArrow_eval. *)
(*   eapply nsteps_l. auto_STLCmuVS_step. asimpl. *)
(*   eapply nsteps_l. auto_STLCmuVS_step. asimpl. *)
(*   rewrite /FixLam /FixLamBodyHelp. asimpl. apply nsteps_O. *)
(* Qed. *)

(* Lemma small_help Γ e τ i : *)
(*   Γ ⊢ₙₒ e : τ → (alter (fun τ => TArrow TUnit τ) i Γ) ⊢ₙₒ e.[upn i ((%0 ())%Eₙₒ .: ren (+1))] : τ. *)
(* Proof. *)
(*   generalize dependent i. *)
(*   generalize dependent τ. *)
(*   generalize dependent Γ. *)
(*   induction e; intros; simpl. *)
(*   - destruct (iter_up_cases x i ((%0)%Eₙₒ ()%Eₙₒ .: ren (+1))) as [[-> lt] | [j [-> ->]]]. *)
(*     + inversion_clear H. constructor. rewrite list_lookup_alter_ne. auto. lia. *)
(*     + inversion_clear H. destruct j. asimpl. *)
(*       econstructor. econstructor. rewrite list_lookup_alter. *)
(*       assert ((i + 0)%nat = i) as eq. lia. rewrite eq in H0. *)
(*       by simplify_option_eq. *)
(*       econstructor. *)
(*       asimpl. constructor. rewrite list_lookup_alter_ne. *)
(*       assert ((i + S j)%nat = S (i + j)%nat) as eq. lia. by rewrite eq in H0. lia. *)
(*   - simpl. inversion_clear H. econstructor. eapply (IHe0 (τ1 :: Γ) τ (S i) H0). by eapply IHe. *)
(*   - simpl. inversion_clear H. econstructor. eapply (IHe (τ1 :: Γ) τ2 (S i) H0). *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe1. by eapply IHe2. *)
(*   - simpl. inversion_clear H; econstructor. *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe1. by eapply IHe2. *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe1. by eapply IHe2. by eapply IHe3. *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe1. by eapply IHe2. *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe1. by eapply IHe2. *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe. *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe. *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe. *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe. *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe. *)
(*       by eapply (IHe0 (τ1 :: Γ) τ (S i)). *)
(*       by eapply (IHe1 (τ2 :: Γ) τ (S i)). *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe. *)
(*   - simpl. inversion_clear H. econstructor. by eapply IHe. *)
(* Qed. *)

(* Lemma FixLamBodyHelp_typed Γ e τ : τ :: Γ ⊢ₙₒ e : τ → Γ ⊢ₙₒ FixLamBodyHelp e : ((TUnit ⟶ τ) ⟶ TUnit ⟶ τ)%Tₙₒ. *)
(* Proof. *)
(*   intro H. *)
(*   apply Lam_typed. apply Lam_typed. change ([TUnit] ++ TUnit ⟶ τ :: Γ ⊢ₙₒ e.[%0 () .: ren (+1)].[ren (+1)] : τ). apply context_weakening. *)
(*   cut ((alter (fun τ => TArrow TUnit τ) 0 (τ :: Γ)) ⊢ₙₒ e.[upn 0 ((%0 ())%Eₙₒ .: ren (+1))] : τ). by asimpl. by apply small_help. *)
(* Qed. *)

(* Lemma FixLam_typed Γ e τ : τ :: Γ ⊢ₙₒ e : τ → Γ ⊢ₙₒ FixLam e : τ. *)
(* Proof. *)
(*   intro H. apply App_typed with (τ1 := TUnit). *)
(*   apply Lam_typed. apply App_typed with (τ1 := TUnit). *)
(*   change ([TUnit] ++ Γ ⊢ₙₒ (FixArrow (FixLamBodyHelp e)).[ren (+1)] : TArrow TUnit τ). apply context_weakening. *)
(*   apply FixArrow_typed. apply FixLamBodyHelp_typed. auto. by econstructor. constructor. *)
(* Qed. *)

(* Lemma FixLam_subst e σ : (FixLam e).[σ] = FixLam e.[up σ]. *)
(* Proof. rewrite /FixLam. by asimpl. Qed. *)

(* Global Opaque FixLam. *)
(* Global Opaque FixArrow. *)
