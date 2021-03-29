From st.lam Require Export types lang typing.
From st.lam.lib Require Export omega fixlam dummy.

(* Local Open Scope Eₙₒ. *)
(* Local Open Scope Tₙₒ. *)

Definition TUniverse_body : type :=
  (( TUnit +
   TBool +
   TInt +
   (TVar 0 × TVar 0) +
   (TVar 0 + TVar 0) +
   (TVar 0 ⟶ TVar 0) ) +
   TRec (TVar 1)
  )%Tₙₒ.

Definition TUniverse : type := TRec TUniverse_body.

Definition TUniverse_unfolded : type := TUniverse_body.[TUniverse/].

From st Require Export lang.

Inductive type_constructor :=
  | TCUnit
  | TCBool
  | TCInt
  | TCProd
  | TCSum
  | TCArrow
  | TCRec.

Definition type_constructor_branch (tc : type_constructor) : type :=
  match tc with
  | TCUnit => TUnit
  | TCBool => TBool
  | TCInt => TInt
  | TCSum => (TUniverse + TUniverse)%Tₙₒ
  | TCProd => (TUniverse × TUniverse)%Tₙₒ
  | TCArrow => (TUniverse ⟶ TUniverse)%Tₙₒ
  | TCRec => TRec TUniverse
  end.

Definition InjTC (tc : type_constructor) (e : expr) : expr :=
  match tc with
  | TCUnit => InjL (InjL (InjL (InjL (InjL (InjL e)))))
  | TCBool => InjL (InjL (InjL (InjL (InjL (InjR e)))))
  | TCInt => InjL (InjL (InjL (InjL (InjR e))))
  | TCProd => InjL (InjL (InjL (InjR e)))
  | TCSum => InjL (InjL (InjR e))
  | TCArrow => InjL (InjR e)
  | TCRec => InjR e
  end.

Definition InjVTC (tc : type_constructor) (v : val) : val :=
  match tc with
  | TCUnit => InjLV (InjLV (InjLV (InjLV (InjLV (InjLV v)))))
  | TCBool => InjLV (InjLV (InjLV (InjLV (InjLV (InjRV v)))))
  | TCInt => InjLV (InjLV (InjLV (InjLV (InjRV v))))
  | TCProd => InjLV (InjLV (InjLV (InjRV v)))
  | TCSum => InjLV (InjLV (InjRV v))
  | TCArrow => InjLV (InjRV v)
  | TCRec => InjRV v
  end.

Lemma InjTC_typed (tc : type_constructor) (e : expr) Γ (d : Γ ⊢ₙₒ e : type_constructor_branch tc) :
  Γ ⊢ₙₒ InjTC tc e : TUniverse_unfolded.
Proof. destruct tc; by repeat constructor. Proof. Qed.

Definition CaseTC (tc : type_constructor) (e : expr) : expr :=
  match tc with
  | TCUnit => Case e (Case %0 (Case %0 (Case %0 (Case %0 (Case %0 %0 Ω) Ω) Ω) Ω) Ω)%Eₙₒ Ω
  | TCBool => Case e (Case %0 (Case %0 (Case %0 (Case %0 (Case %0 Ω %0) Ω) Ω) Ω) Ω)%Eₙₒ Ω
  | TCInt => Case e (Case %0 (Case %0 (Case %0 (Case %0 Ω %0) Ω) Ω) Ω)%Eₙₒ Ω
  | TCProd => Case e (Case %0 (Case %0 (Case %0 Ω %0) Ω) Ω)%Eₙₒ Ω
  | TCSum => Case e (Case %0 (Case %0 Ω %0) Ω)%Eₙₒ Ω
  | TCArrow => Case e (Case %0 Ω %0)%Eₙₒ Ω
  | TCRec => (Case e Ω %0)%Eₙₒ
  end.

Lemma CaseTC_typed (tc : type_constructor) (e : expr) Γ (d : Γ ⊢ₙₒ e : TUniverse_unfolded) :
  Γ ⊢ₙₒ CaseTC tc e : type_constructor_branch tc.
Proof. destruct tc; repeat eapply Case_typed; (by constructor) || (by apply Ω_typed) || (try by eapply d). Qed.

(* Definition inject (tc : type_constructor) (e : expr) : expr := Fold (InjTC tc e). *)

(* Lemma inject_typed (tc : type_constructor) (e : expr) Γ (d : Γ ⊢ₙₒ e : type_constructor_branch tc) : *)
(*   Γ ⊢ₙₒ inject tc e : TUniverse. *)
(* Proof. by apply Fold_typed, InjTC_typed. Qed. *)

(* Definition extract (tc : type_constructor) (e : expr) : expr := (CaseTC tc (Unfold e)). *)

(* Lemma extract_typed (tc : type_constructor) (e : expr) Γ (d : Γ ⊢ₙₒ e : TUniverse) : *)
(*   Γ ⊢ₙₒ extract tc e : type_constructor_branch tc. *)
(* Proof. by apply CaseTC_typed, Unfold_typed. Qed. *)

Definition inject (tc : type_constructor) : expr := Lam (Fold (InjTC tc %0))%Eₙₒ.

Lemma inject_typed (tc : type_constructor) Γ :
  Γ ⊢ₙₒ inject tc : type_constructor_branch tc ⟶ TUniverse.
Proof. by apply Lam_typed, Fold_typed, InjTC_typed, Var_typed. Qed.

Definition extract (tc : type_constructor) : expr := Lam (CaseTC tc (Unfold %0))%Eₙₒ.

Lemma extract_typed (tc : type_constructor) Γ :
  Γ ⊢ₙₒ extract tc : TUniverse ⟶ type_constructor_branch tc.
Proof. by apply Lam_typed, CaseTC_typed, Unfold_typed, Var_typed. Qed.

Inductive direction :=
  | upward
  | downward.

Fixpoint embed_project_pair (xs : list var) (τ : type) : expr :=
  match τ with
  | TUnit => (inject TCUnit , extract TCUnit)%Eₙₒ
  | TBool => (inject TCBool , extract TCBool)%Eₙₒ
  | TInt => (inject TCInt , extract TCInt)%Eₙₒ
  | TProd τ1 τ2 => (Lam (LetIn (Fst %0) (LetIn (Snd %1)
                                              (inject TCProd (Fst (embed_project_pair ((+3) <$> xs) τ1) %1, Fst (embed_project_pair ((+3) <$> xs) τ2) %0)))) ,
                   Lam (LetIn (extract TCProd %0) (LetIn (Fst %0) (LetIn (Snd %1)
                                                                         (Snd (embed_project_pair ((+4) <$> xs) τ1) %1 , Snd (embed_project_pair ((+4) <$> xs) τ2) %0)))))%Eₙₒ
  | TSum τ1 τ2 => (Lam (Case %0 (inject TCSum (InjL (Fst (embed_project_pair ((+2) <$> xs) τ1) %0))) (inject TCSum (InjR (Fst (embed_project_pair ((+2) <$> xs) τ2) %0)))) ,
                  (Lam (Case (extract TCSum %0) (InjL (Snd (embed_project_pair ((+2) <$> xs) τ1) %0)) (InjR (Snd (embed_project_pair ((+2) <$> xs) τ2) %0)))))%Eₙₒ
  | TArrow τ1 τ2 => (Lam (inject TCArrow (Lam (Fst (embed_project_pair ((+2) <$> xs) τ2) (%1 (Snd (embed_project_pair ((+2) <$> xs) τ1) %0))))) ,
                    (Lam (Lam (Snd (embed_project_pair ((+2) <$> xs) τ2) (extract TCArrow %1 (Fst (embed_project_pair ((+2) <$> xs) τ1) %0))))))%Eₙₒ
  | TRec τ => FixLam (Lam (inject TCRec (Fold (Fst (embed_project_pair (1 :: ((+2) <$> xs)) τ) (Unfold %0)))) ,
                     Lam (Fold (Snd (embed_project_pair (1 :: ((+2) <$> xs)) τ) (Unfold (extract TCRec %0)))))%Eₙₒ
  | TVar X => match xs !! X with
             | Some x => Var x
             | None => dummy
             end
  | TForall τ => dummy
  end.

Lemma embed_project_pair_typed_gen (τ : type) (τs : list type) (pτn : Closed_n (length τs) τ) (xs : list var) Γ
      (P : Forall2 (fun x τ => Γ !! x = Some ((τ ⟶ TUniverse) × (TUniverse ⟶ τ))%Tₙₒ) xs τs) :
  Γ ⊢ₙₒ (embed_project_pair xs τ) : ((τ.[subst_list τs] ⟶ TUniverse) × (TUniverse ⟶ τ.[subst_list τs])).
Proof.
  generalize dependent Γ.
  generalize dependent xs.
  generalize dependent τs.
  induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τb IHτb | X | sadf ] ;
    intros τs Cnτ xs Γ Pxsτs; try by repeat (apply Pair_typed || apply inject_typed || apply extract_typed).
  - (* TProd *) assert (pCτ1 : Closed_n (length τs) τ1). admit. assert (pCτ2 : Closed_n (length τs) τ2). admit.
    specialize (IHτ1 τs pCτ1). specialize (IHτ2 τs pCτ2).
    apply Pair_typed; fold embed_project_pair;
      repeat (apply IHτ1 || apply IHτ2 || apply inject_typed || apply extract_typed || econstructor); by apply Forall2_fmap_l.
  - (* TSum *) assert (pCτ1 : Closed_n (length τs) τ1). admit. assert (pCτ2 : Closed_n (length τs) τ2). admit.
    specialize (IHτ1 τs pCτ1). specialize (IHτ2 τs pCτ2).
    apply Pair_typed; fold embed_project_pair;
      repeat (apply IHτ1 || apply IHτ2 || apply inject_typed || apply (extract_typed TCSum) || econstructor); by apply Forall2_fmap_l.
  - (* TArrow *) assert (pCτ1 : Closed_n (length τs) τ1). admit. assert (pCτ2 : Closed_n (length τs) τ2). admit.
    specialize (IHτ1 τs pCτ1). specialize (IHτ2 τs pCτ2).
    apply Pair_typed; fold embed_project_pair;
      repeat (apply IHτ1 || apply IHτ2 || apply inject_typed || apply (extract_typed TCArrow) || econstructor); by apply Forall2_fmap_l.
  - (* TRec *) specialize (IHτb ((TRec τb).[subst_list τs] :: τs)).
    assert (Closed_n (S (length τs)) τb) as CSnτb. admit. specialize (IHτb CSnτb).
    assert (τb.[up (subst_list τs)].[TRec τb.[up (subst_list τs)]/] = τb.[subst_list ((TRec τb).[subst_list τs] :: τs)]) as eqn.
      { rewrite -subst_list_cons_closed_S_n_type. by asimpl. done. }
    apply FixLam_typed. fold (embed_project_pair). apply Pair_typed.
    + apply Lam_typed. apply App_typed with (τ1 := TRec TUniverse). apply inject_typed. apply Fold_typed.
      apply App_typed with (τ1 := τb.[up (subst_list τs)].[TRec τb.[up (subst_list τs)]/]).
      eapply Fst_typed. rewrite eqn. apply IHτb. simpl. apply Forall2_cons. split.
      apply Forall2_fmap_l. apply (Forall2_impl _ _ _ _ Pxsτs). by simpl.
      apply Unfold_typed. by apply Var_typed.
    + apply Lam_typed. apply Fold_typed. apply App_typed with (τ1 := TUniverse). eapply Snd_typed.
      rewrite eqn. apply IHτb. simpl. apply Forall2_cons. split.
      apply Forall2_fmap_l. apply (Forall2_impl _ _ _ _ Pxsτs). by simpl.
      assert (TUniverse = TUniverse.[TRec TUniverse/]) as ->. intros; by asimpl. apply Unfold_typed. eapply App_typed. apply extract_typed. by apply Var_typed.
  - (* TVar *) assert (X < (length τs)) as pxltlτs. admit. simpl. destruct (xs !! X) as [x |] eqn:eq.
    + apply Var_typed. rewrite /subst_list. destruct (τs !! X) as [τ |] eqn:eq2.
      * simpl. apply (Forall2_lookup_lr _ _ _ X _ _ Pxsτs eq eq2).
      * exfalso. assert (length xs = length τs). by eapply Forall2_length.
        assert (length τs ≤ X). by eapply lookup_ge_None_1.
        assert (X < length xs). by eapply lookup_lt_Some. lia.
    + exfalso. assert (length xs = length τs). by eapply Forall2_length.
        assert (length xs ≤ X). by eapply lookup_ge_None_1. lia.
Admitted.

Lemma embed_project_pair_typed (τ : type) (pτ : Closed τ) Γ :
  Γ ⊢ₙₒ (embed_project_pair [] τ) : ((τ ⟶ TUniverse) × (TUniverse ⟶ τ)).
Proof.
  cut (Γ ⊢ₙₒ embed_project_pair [] τ : (τ.[subst_list []] ⟶ TUniverse) × (TUniverse ⟶ τ.[subst_list []])); first by rewrite pτ.
  by apply embed_project_pair_typed_gen.
Qed.

(* (* If we somehow end up only allowing closed types... *) *)

(* Lemma embed_project_pair_typed_closed_gen (τ : type) (τs : list type) (pτn : Closed_n (length τs) τ) (xs : list var) Γ *)
(*       (P : Forall2 (fun x τ => Closed τ ∧ Γ !! x = Some ((τ ⟶ TUniverse) × (TUniverse ⟶ τ))%Tₙₒ) xs τs) : *)
(*   Γ ⊢ₙₒ (embed_project_pair xs τ) : ((τ.[subst_list τs] ⟶ TUniverse) × (TUniverse ⟶ τ.[subst_list τs])). *)
(* Proof. *)
(*   generalize dependent Γ. *)
(*   generalize dependent xs. *)
(*   generalize dependent τs. *)
(*   induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τb IHτb | X | sadf ] ; *)
(*     intros τs Cnτ xs Γ Pxsτs; try by repeat (apply Pair_typed || apply inject_typed || apply extract_typed). *)
(*   - (* TProd *) assert (pCτ1 : Closed_n (length τs) τ1). admit. assert (pCτ2 : Closed_n (length τs) τ2). admit. *)
(*     specialize (IHτ1 τs pCτ1). specialize (IHτ2 τs pCτ2). *)
(*     apply Pair_typed; fold embed_project_pair; *)
(*       repeat (apply IHτ1 || apply IHτ2 || apply inject_typed || apply extract_typed || econstructor); by apply Forall2_fmap_l. *)
(*   - (* TSum *) assert (pCτ1 : Closed_n (length τs) τ1). admit. assert (pCτ2 : Closed_n (length τs) τ2). admit. *)
(*     specialize (IHτ1 τs pCτ1). specialize (IHτ2 τs pCτ2). *)
(*     apply Pair_typed; fold embed_project_pair; *)
(*       repeat (apply IHτ1 || apply IHτ2 || apply inject_typed || apply (extract_typed TCSum) || econstructor); by apply Forall2_fmap_l. *)
(*   - (* TArrow *) assert (pCτ1 : Closed_n (length τs) τ1). admit. assert (pCτ2 : Closed_n (length τs) τ2). admit. *)
(*     specialize (IHτ1 τs pCτ1). specialize (IHτ2 τs pCτ2). *)
(*     apply Pair_typed; fold embed_project_pair; *)
(*       repeat (apply IHτ1 || apply IHτ2 || apply inject_typed || apply (extract_typed TCArrow) || econstructor); by apply Forall2_fmap_l. *)
(*   - (* TRec *) specialize (IHτb ((TRec τb).[subst_list τs] :: τs)). *)
(*     assert (Closed (TRec τb).[subst_list τs]) as pCμτb. admit. *)
(*     assert (Closed_n (S (length τs)) τb) as CSnτb. admit. specialize (IHτb CSnτb). *)
(*     assert (τb.[up (subst_list τs)].[TRec τb.[up (subst_list τs)]/] = τb.[subst_list ((TRec τb).[subst_list τs] :: τs)]) as eqn. *)
(*       { rewrite -subst_list_cons_closed_S_n_type. by asimpl. done. } *)
(*     apply FixLam_typed. fold (embed_project_pair). apply Pair_typed. *)
(*     + apply Lam_typed. apply App_typed with (τ1 := TRec TUniverse). apply inject_typed. apply Fold_typed. *)
(*       apply App_typed with (τ1 := τb.[up (subst_list τs)].[TRec τb.[up (subst_list τs)]/]). *)
(*       eapply Fst_typed. rewrite eqn. apply IHτb. apply Forall2_cons. split; try by simpl. *)
(*       apply Forall2_fmap_l. apply (Forall2_impl _ _ _ _ Pxsτs). by simpl. *)
(*       apply Unfold_typed. by apply Var_typed. *)
(*     + apply Lam_typed. apply Fold_typed. apply App_typed with (τ1 := TUniverse). eapply Snd_typed. *)
(*       rewrite eqn. apply IHτb. simpl. apply Forall2_cons. split; try by simpl. *)
(*       apply Forall2_fmap_l. apply (Forall2_impl _ _ _ _ Pxsτs). by simpl. *)
(*       assert (TUniverse = TUniverse.[TRec TUniverse/]) as ->. intros; by asimpl. apply Unfold_typed. eapply App_typed. apply extract_typed. by apply Var_typed. *)
(*   - (* TVar *) assert (X < (length τs)) as pxltlτs. admit. simpl. destruct (xs !! X) as [x |] eqn:eq. *)
(*     + apply Var_typed. rewrite /subst_list. destruct (τs !! X) as [τ |] eqn:eq2. *)
(*       * simpl. apply (Forall2_lookup_lr _ _ _ X _ _ Pxsτs eq eq2). *)
(*       * exfalso. assert (length xs = length τs). by eapply Forall2_length. *)
(*         assert (length τs ≤ X). by eapply lookup_ge_None_1. *)
(*         assert (X < length xs). by eapply lookup_lt_Some. lia. *)
(*     + exfalso. assert (length xs = length τs). by eapply Forall2_length. *)
(*         assert (length xs ≤ X). by eapply lookup_ge_None_1. lia. *)
(* Admitted. *)
