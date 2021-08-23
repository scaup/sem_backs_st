From st.STLCmuST Require Import types lang.

Definition binop_res_type (op : bin_op) : type :=
  match op with
  | PlusOp => TInt | MinusOp => TInt
  | EqOp => TBool | LeOp => TBool | LtOp => TBool
  end.

Reserved Notation "Γ ⊢ₛₜ e : τ" (at level 74, e, τ at next level).

Inductive typed (Γ : list type) : expr → type → Prop :=
 | Var_typed x τ : Γ !! x = Some τ → Γ ⊢ₛₜ Var x : τ
 | Unit_typed : Γ ⊢ₛₜ Lit (LitUnit) : TUnit
 | Bool_typed b : Γ ⊢ₛₜ Lit (LitBool b) : TBool
 | Int_typed z : Γ ⊢ₛₜ Lit (LitInt z) : TInt
 | BinOp_typed op e1 e2 :
     Γ ⊢ₛₜ e1 : TInt → Γ ⊢ₛₜ e2 : TInt → Γ ⊢ₛₜ BinOp op e1 e2 : binop_res_type op
 | Seq_typed e1 e2 τ :
     Γ ⊢ₛₜ e1 : TUnit → Γ ⊢ₛₜ e2 : τ → Γ ⊢ₛₜ Seq e1 e2 : τ
 | Pair_typed e1 e2 τ1 τ2 :
    Γ ⊢ₛₜ e1 : τ1 → Γ ⊢ₛₜ e2 : τ2 → Γ ⊢ₛₜ Pair e1 e2 : TProd τ1 τ2
 | Fst_typed e τ1 τ2 : Γ ⊢ₛₜ e : TProd τ1 τ2 → Γ ⊢ₛₜ Fst e : τ1
 | Snd_typed e τ1 τ2 : Γ ⊢ₛₜ e : TProd τ1 τ2 → Γ ⊢ₛₜ Snd e : τ2
 | InjL_typed e τ1 τ2 : Γ ⊢ₛₜ e : τ1 → Γ ⊢ₛₜ InjL e : TSum τ1 τ2
 | InjR_typed e τ1 τ2 : Γ ⊢ₛₜ e : τ2 → Γ ⊢ₛₜ InjR e : TSum τ1 τ2
 | Case_typed e0 e1 e2 τ1 τ2 τ3 :
    Γ ⊢ₛₜ e0 : TSum τ1 τ2 → τ1 :: Γ ⊢ₛₜ e1 : τ3 → τ2 :: Γ ⊢ₛₜ e2 : τ3 →
    Γ ⊢ₛₜ Case e0 e1 e2 : τ3
 | If_typed e0 e1 e2 τ :
    Γ ⊢ₛₜ e0 : TBool → Γ ⊢ₛₜ e1 : τ → Γ ⊢ₛₜ e2 : τ → Γ ⊢ₛₜ If e0 e1 e2 : τ
 | LetIn_typed e2 e1 τ1 τ2 :
    τ1 :: Γ ⊢ₛₜ e2 : τ2 → Γ ⊢ₛₜ e1 : τ1 → Γ ⊢ₛₜ LetIn e1 e2 : τ2
 | Lam_typed e τ1 τ2 :
    τ1 :: Γ ⊢ₛₜ e : τ2 → Γ ⊢ₛₜ Lam e : TArrow τ1 τ2
 (* | Fix_typed e τ : *)
    (* Γ ⊢ₛₜ e : TArrow τ τ → Γ ⊢ₛₜ Fix e : τ *)
 (* | Rec_typed e τ1 τ2 : *)
    (* TArrow τ1 τ2 :: τ1 :: Γ ⊢ₛₜ e : τ2 → Γ ⊢ₛₜ Rec e : TArrow τ1 τ2 *)
 | App_typed e1 e2 τ1 τ2 :
    Γ ⊢ₛₜ e1 : TArrow τ1 τ2 → Γ ⊢ₛₜ e2 : τ1 → Γ ⊢ₛₜ App e1 e2 : τ2
 (* | TLam_typed e τ : *)
    (* subst (ren (+1)) <$> Γ ⊢ₛₜ e : τ → Γ ⊢ₛₜ TLam e : TForall τ *)
 (* | TApp_typed e τ τ' : Γ ⊢ₛₜ e : TForall τ → Γ ⊢ₛₜ TApp e : τ.[τ'/] *)
 | Fold_typed e τ : Γ ⊢ₛₜ e : τ.[TRec τ/] → Γ ⊢ₛₜ Fold e : TRec τ
 | Unfold_typed e τ : Γ ⊢ₛₜ e : TRec τ → Γ ⊢ₛₜ Unfold e : τ.[TRec τ/]
 | Alloc_typed e τ ρ: Γ ⊢ₛₜ e : τ → Γ ⊢ₛₜ Alloc e : TST ρ (TSTref ρ τ)
 | Read_typed e τ ρ : Γ ⊢ₛₜ e : TSTref ρ τ → Γ ⊢ₛₜ Read e : TST ρ τ
 | Write_typed e e' τ ρ :
    Γ ⊢ₛₜ e : TSTref ρ τ → Γ ⊢ₛₜ e' : τ → Γ ⊢ₛₜ Write e e' : TST ρ TUnit
 | Bind_typed e1 e2 ρ τ1 τ2 :
    Γ ⊢ₛₜ e1 : TST ρ τ1 -> Γ ⊢ₛₜ e2 : (TArrow τ1 (TST ρ τ2)) ->
    Γ ⊢ₛₜ (Bind e1 e2) : (TST ρ τ2)
 | Return_typed e ρ τ : Γ ⊢ₛₜ e : τ -> Γ ⊢ₛₜ Return e : TST ρ τ
 | RunST_typed e τ :
     subst (ren (+1)) <$>Γ ⊢ₛₜ e : TST (TVar 0) τ.[ren (+1)] ->
     Γ ⊢ₛₜ RunST e : τ
 | Compare_typed e1 e2 ρ τ:
     Γ ⊢ₛₜ e1 : TSTref ρ τ → Γ ⊢ₛₜ e2 : TSTref ρ τ → Γ ⊢ₛₜ Compare e1 e2 : TBool
where "Γ ⊢ₛₜ e : τ" := (typed Γ e τ%Tₛₜ).

Lemma typed_subst_invariant Γ e τ s1 s2 :
  Γ ⊢ₛₜ e : τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ x Γ, x < length (subst (ren (+1)) <$> Γ) → x < length Γ).
  { intros ??. by rewrite fmap_length. }
  assert (∀ {A} `{Ids A} `{Rename A} (s1 s2 : nat → A) x,
    (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal lia. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with lia;
  apply IHHtyped; by rewrite fmap_length.
Qed.
Lemma n_closed_invariant n (e : expr) s1 s2 :
  (∀ f, e.[upn n f] = e) → (∀ x, x < n → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Hnc. specialize (Hnc (ren (+1))).
  revert n Hnc s1 s2.
  induction e => m Hmc s1 s2 H1; asimpl in *; try f_equal;
    try (match goal with H : _ |- _ => eapply H end; eauto;
         try inversion Hmc; try match goal with H : _ |- _ => by rewrite H end;
         fail).
  - apply H1. rewrite iter_up in Hmc. destruct lt_dec; try lia.
    asimpl in *. cbv in x. replace (m + (x - m)) with x in Hmc by lia.
    inversion Hmc; lia.
  - apply (IHe0 (S m)).
    + inversion Hmc. by do 2 rewrite H2.
    + intro n. destruct n eqn:eq. by asimpl.
      intro neq. asimpl. rewrite (H1 n0). by simpl. lia.
  - unfold upn in *.
    apply (IHe (S m)).
    + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end.
    + intros [|[|x]] H2; [by cbv| |].
      asimpl; rewrite H1; auto with lia.
      asimpl; rewrite H1; auto with lia.
  (* - unfold upn in *. *)
  (*   change (e.[up (up (upn m (ren (+1))))]) with *)
  (*   (e.[iter (S (S m)) up (ren (+1))]) in *. *)
  (*   apply (IHe (S (S m))). *)
  (*   + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end. *)
  (*   + intros [|[|x]] H2; [by cbv|by cbv |]. *)
  (*     asimpl; rewrite H1; auto with lia. *)
  - change (e1.[up (upn m (ren (+1)))]) with
    (e1.[iter (S m) up (ren (+1))]) in *.
    apply (IHe0 (S m)).
    + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end.
    + intros [|x] H2; [by cbv |].
      asimpl; rewrite H1; auto with lia.
  - change (e2.[up (upn m (ren (+1)))]) with
    (e2.[upn (S m) (ren (+1))]) in *.
    apply (IHe1 (S m)).
    + inversion Hmc; match goal with H : _ |- _ => (by rewrite H) end.
    + intros [|x] H2; [by cbv |].
      asimpl; rewrite H1; auto with lia.
Qed.

Definition env_subst (vs : list val) (x : var) : expr :=
  from_option id (Var x) (of_val <$> vs !! x).

Lemma typed_n_closed Γ τ e : Γ ⊢ₛₜ e : τ → (∀ f, e.[upn (length Γ) f] = e).
Proof.
  intros H. induction H => f; asimpl; simpl in *; auto with f_equal.
  - apply lookup_lt_Some in H. rewrite iter_up. destruct lt_dec; auto with lia.
  (* - f_equal. apply IHtyped. *)
  - by f_equal; rewrite map_length in IHtyped.
  (* - by f_equal; rewrite map_length in IHtyped. *)
Qed.

Lemma n_closed_subst_head_simpl n e w ws :
  (∀ f, e.[upn n f] = e) →
  S (length ws) = n →
  e.[of_val w .: env_subst ws] = e.[env_subst (w :: ws)].
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply n_closed_invariant; eauto=> /= -[|x] ? //=.
  destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first lia; simpl.
  by rewrite Hv.
Qed.

Lemma typed_subst_head_simpl Δ τ e w ws :
  Δ ⊢ₛₜ e : τ → length Δ = S (length ws) →
  e.[of_val w .: env_subst ws] = e.[env_subst (w :: ws)].
Proof. eauto using n_closed_subst_head_simpl, typed_n_closed. Qed.

Lemma n_closed_subst_head_simpl_2 n e w w' ws :
  (∀ f, e.[upn n f] = e) → (S (S (length ws))) = n →
  e.[of_val w .: of_val w' .: env_subst ws] = e.[env_subst (w :: w' :: ws)].
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply n_closed_invariant; eauto => /= -[|[|x]] H3 //=.
  destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first lia; simpl.
  by rewrite Hv.
Qed.

Lemma typed_subst_head_simpl_2 Δ τ e w w' ws :
  Δ ⊢ₛₜ e : τ → length Δ = 2 + length ws →
  e.[of_val w .: of_val w' .: env_subst ws] = e.[env_subst (w :: w' :: ws)].
Proof. eauto using n_closed_subst_head_simpl_2, typed_n_closed. Qed.

Lemma n_closed_subst_head_simpl_3 n e w1 w2 w3 ws :
  (∀ f, e.[upn n f] = e) → S (S (S (length ws))) = n →
  e.[of_val w1 .: of_val w2 .: of_val w3 .: env_subst ws] =
  e.[env_subst (w1 :: w2 :: w3 :: ws)].
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply n_closed_invariant; eauto => /= -[|[|[|x]]] H3 //=.
  destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first lia; simpl.
  by rewrite Hv.
Qed.

Lemma typed_subst_head_simpl_3 Δ τ e w1 w2 w3 ws :
  Δ ⊢ₛₜ e : τ → length Δ = 3 + length ws →
  e.[of_val w1 .: of_val w2 .: of_val w3 .:env_subst ws] =
  e.[env_subst (w1 :: w2 :: w3 :: ws)].
Proof. eauto using n_closed_subst_head_simpl_3, typed_n_closed. Qed.

Lemma n_closed_subst_head_simpl_4 n e w1 w2 w3 w4 ws :
  (∀ f, e.[upn n f] = e) → S (S (S (S (length ws)))) = n →
  e.[of_val w1 .: of_val w2 .: of_val w3 .: of_val w4 .: env_subst ws] =
  e.[env_subst (w1 :: w2 :: w3 :: w4 :: ws)].
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply n_closed_invariant; eauto => /= -[|[|[|[|x]]]] H3 //=.
  destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first lia; simpl.
  by rewrite Hv.
Qed.

Lemma typed_subst_head_simpl_4 Δ τ e w1 w2 w3 w4 ws :
  Δ ⊢ₛₜ e : τ → length Δ = 4 + length ws →
  e.[of_val w1 .: of_val w2 .: of_val w3 .: of_val w4 .:env_subst ws] =
  e.[env_subst (w1 :: w2 :: w3 :: w4 :: ws)].
Proof. eauto using n_closed_subst_head_simpl_4, typed_n_closed. Qed.

Lemma empty_env_subst e : e.[env_subst []] = e.
Proof. change (env_subst []) with (@ids expr _). by asimpl. Qed.

(** Weakening *)
Lemma context_gen_weakening ξ Γ' Γ e τ :
  Γ' ++ Γ ⊢ₛₜ e : τ →
  Γ' ++ ξ ++ Γ ⊢ₛₜ e.[upn (length Γ') (ren (+ (length ξ)))] : τ.
Proof.
  intros H1.
  remember (Γ' ++ Γ) as Ξ. revert Γ' Γ ξ HeqΞ.
  induction H1 => Γ1 Γ2 ξ HeqΞ; subst; asimpl in *; eauto using typed.
  - rewrite iter_up; destruct lt_dec as [Hl | Hl].
    + constructor. rewrite lookup_app_l; trivial. by rewrite lookup_app_l in H.
    + asimpl. constructor. rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r; auto with lia.
      rewrite lookup_app_r in H; auto with lia.
      match goal with
        |- _ !! ?A = _ => by replace A with (x - length Γ1) by lia
      end.
  - econstructor; eauto. by apply (IHtyped2 (_::_)). by apply (IHtyped3 (_::_)).
  - econstructor; eauto. by apply (IHtyped1 (_::_)).
  - econstructor; eauto. by apply (IHtyped (_::_)).
  (* - constructor. by apply (IHtyped (_ :: _ :: _)). *)
  - constructor.
    specialize (IHtyped
      (subst (ren (+1)) <$> Γ1) (subst (ren (+1)) <$> Γ2) (subst (ren (+1)) <$> ξ)).
    asimpl in *. rewrite ?map_length in IHtyped.
    repeat rewrite fmap_app. apply IHtyped.
    by repeat rewrite fmap_app.
  (* - constructor; eauto. *)
  (*   specialize (IHtyped *)
  (*     (subst (ren (+1)) <$> Γ1) (subst (ren (+1)) <$> Γ2) (subst (ren (+1)) <$> ξ)). *)
  (*   asimpl in *. rewrite ?map_length in IHtyped. *)
  (*   repeat rewrite fmap_app. apply IHtyped. *)
  (*   by repeat rewrite fmap_app. *)
Qed.

Lemma context_weakening ξ Γ e τ :
  Γ ⊢ₛₜ e : τ → ξ ++ Γ ⊢ₛₜ e.[(ren (+ (length ξ)))] : τ.
Proof. eapply (context_gen_weakening _ []). Qed.

Lemma context_gen_strengthening ξ Γ' Γ e τ :
  Γ' ++ ξ ++ Γ ⊢ₛₜ e.[upn (length Γ') (ren (+ (length ξ)))] : τ →
  Γ' ++ Γ ⊢ₛₜ e : τ.
Proof.
  intros Ht.
  remember (Γ' ++ ξ ++ Γ) as Ξ.
  remember e.[upn (length Γ') (ren (+length ξ))] as e'.
  revert Γ' Γ ξ HeqΞ e Heqe'.
  induction Ht => Γ1 Γ2 ξ HeqΞ t Heqe'; subst;
    (destruct t; inversion Heqe' as [Heqe'2]; subst;
     asimpl in Heqe'; eauto using typed;
     first try (rewrite iter_up in Heqe'; destruct lt_dec;
            inversion Heqe'; subst; fail)).
  - econstructor.
    rewrite iter_up in Heqe'2; destruct lt_dec; asimpl in Heqe'2.
    + inversion Heqe'2; subst. rewrite lookup_app_l; auto.
      rewrite lookup_app_l in H; auto.
    + inversion Heqe'2; subst.
      rewrite ?lookup_app_r in H; auto with lia.
      rewrite lookup_app_r; auto with lia.
      replace (length Γ1 + length ξ + (x0 - length Γ1) - length Γ1 - length ξ)
      with (x0 - length Γ1) in H; auto with lia.
  - econstructor; eauto. by eapply (IHHt2 (_::_)). by eapply (IHHt3 (_::_)).
  - econstructor; eauto. by eapply (IHHt1 (_::_)).
  - econstructor; eauto. by eapply (IHHt (_::_)).
  (* - econstructor; eauto. by eapply (IHHt (_ :: _::_)). *)
  - constructor.
    specialize (IHHt
      (subst (ren (+1)) <$> Γ1) (subst (ren (+1)) <$> Γ2)
      (subst (ren (+1)) <$> ξ)).
    rewrite !map_length in IHHt.
    repeat rewrite fmap_app. apply IHHt; auto.
    by repeat rewrite fmap_app.
  (* - constructor. *)
  (*   specialize (IHHt *)
  (*     (subst (ren (+1)) <$> Γ1) (subst (ren (+1)) <$> Γ2) *)
  (*     (subst (ren (+1)) <$> ξ)). *)
  (*   rewrite !map_length in IHHt. *)
  (*   repeat rewrite fmap_app. apply IHHt; auto. *)
  (*   by repeat rewrite fmap_app. *)
Qed.

Lemma context_strengthening ξ Γ e τ :
  ξ ++ Γ ⊢ₛₜ e.[(ren (+ (length ξ)))] : τ → Γ ⊢ₛₜ e : τ.
Proof. eapply (context_gen_strengthening _ []). Qed.

Definition swap_list n m : list nat := (seq n m) ++ seq 0 n.

Definition lookup_n (l : list nat) i : nat :=
  match l !! i with
  | Some x => x
  | None => i
  end.

Lemma lookup_n_swap_list_out n m i :
  i ≥ n + m → lookup_n (swap_list n m) i = i.
Proof.
  rewrite /lookup_n /swap_list => Hge.
  rewrite lookup_ge_None_2; first done.
  rewrite app_length !seq_length; lia.
Qed.

Lemma lookup_n_swap_list_in n m i :
  i < n + m → lookup_n (swap_list n m) i < n + m.
Proof.
  rewrite /lookup_n /swap_list => Hge.
  edestruct (@lookup_lt_is_Some_2 nat (seq n m ++ seq 0 n) i) as [x Hx].
  { rewrite app_length !seq_length; lia. }
  rewrite Hx.
  destruct (decide (i < m)).
  - rewrite lookup_app_l in Hx; last by rewrite seq_length.
    apply lookup_seq in Hx; lia.
  - rewrite lookup_app_r in Hx; last rewrite seq_length; auto with lia.
    apply lookup_seq in Hx; lia.
Qed.

Lemma lookup_n_swap_list_r n m i :
  i < m → lookup_n (swap_list n m) i = n + i.
Proof.
  rewrite /lookup_n /swap_list => Hlt.
  rewrite lookup_app_l; last by rewrite seq_length.
  rewrite lookup_seq_lt; auto.
Qed.

Lemma lookup_n_swap_list_l n m i :
  m ≤ i → i < n + m → lookup_n (swap_list n m) i = (i - m).
Proof.
  rewrite /lookup_n /swap_list => Hle Hlt.
  rewrite lookup_app_r; last rewrite seq_length; try lia.
  rewrite lookup_seq_lt; rewrite ?seq_length; auto with lia.
Qed.

Lemma context_swap_typed Γ' ξ' ξ Γ e τ :
  Γ' ++ ξ' ++ ξ ++ Γ ⊢ₛₜ e : τ →
  Γ' ++ ξ ++ ξ' ++ Γ ⊢ₛₜ e.[upn (length Γ') (ren (lookup_n (swap_list (length ξ) (length ξ'))))] : τ.
Proof.
  intros Ht.
  remember (Γ' ++ ξ' ++ ξ ++ Γ) as Ξ. revert Γ' ξ' ξ Γ HeqΞ.
  induction Ht => Γ' ξ' ξ Γ1 HeqΞ; simpl; eauto using typed.
  - subst. rewrite iter_up; destruct lt_dec as [Hl | Hl].
    + econstructor.
      match goal with
        H : _ !! _ = Some _ |- _ => revert H
      end.
      rewrite !lookup_app_l; auto.
    + constructor. simpl. rewrite lookup_app_r; auto with lia.
      replace (length Γ' + lookup_n (swap_list (length ξ) (length ξ')) (x - length Γ') - length Γ') with
      (lookup_n (swap_list (length ξ) (length ξ')) (x - length Γ')) by lia.
      match goal with
        H : _ !! _ = Some _ |- _ =>
        rewrite lookup_app_r in H; auto with lia; rename H into Hlu
      end.
      destruct (decide ((x - length Γ') < (length ξ) + (length ξ'))).
      * rewrite app_assoc. rewrite app_assoc in Hlu.
        rewrite lookup_app_l; rewrite lookup_app_l in Hlu;
          rewrite ?app_length; eauto with lia; try apply lookup_n_swap_list_in; auto.
        destruct (decide ((x - length Γ') < (length ξ'))).
        -- rewrite lookup_n_swap_list_r; auto.
           rewrite lookup_app_r; rewrite lookup_app_l in Hlu; auto with lia.
           replace (length ξ + (x - length Γ') - length ξ) with (x - length Γ') by lia.
           done.
        -- rewrite lookup_n_swap_list_l; auto with lia.
           rewrite lookup_app_l; rewrite lookup_app_r in Hlu; auto with lia.
      * rewrite lookup_n_swap_list_out; auto with lia.
        rewrite app_assoc. rewrite app_assoc in Hlu.
        rewrite lookup_app_r; rewrite lookup_app_r in Hlu;
          rewrite ?app_length; try rewrite ?app_length in Hlu; auto with lia.
        replace (x - length Γ' - (length ξ + length ξ')) with
        (x - length Γ' - (length ξ' + length ξ)) by lia.
        done.
  - econstructor; eauto.
    + eapply (IHHt2 (_ :: _)). by simpl; f_equal.
    + eapply (IHHt3 (_ :: _)). by simpl; f_equal.
  - econstructor.
    + apply (IHHt1 (_ :: _)). by simpl; repeat f_equal.
    + apply (IHHt2). by simpl; repeat f_equal.
  - econstructor.
    + apply (IHHt (_ :: _)). by simpl; repeat f_equal.
  (* - econstructor. apply (IHHt (_ :: _ :: _)). by simpl; repeat f_equal. *)
  - constructor.
    specialize (IHHt
      (subst (ren (+1)) <$> Γ') (subst (ren (+1)) <$> ξ')
      (subst (ren (+1)) <$> ξ) (subst (ren (+1)) <$> Γ1)).
    asimpl in *. rewrite ?map_length in IHHt.
    repeat rewrite fmap_app. eapply IHHt.
    by rewrite HeqΞ; repeat rewrite fmap_app.
  (* - econstructor; eauto. *)
  (*   specialize (IHHt *)
  (*     (subst (ren (+1)) <$> Γ') (subst (ren (+1)) <$> ξ') *)
  (*     (subst (ren (+1)) <$> ξ) (subst (ren (+1)) <$> Γ1)). *)
  (*   asimpl in *. rewrite ?map_length in IHHt. *)
  (*   repeat rewrite fmap_app. eapply IHHt. *)
  (*   by rewrite HeqΞ; repeat rewrite fmap_app. *)
Qed.

Lemma closed_context_weakening ξ Γ e τ :
  (∀ f, e.[f] = e) → Γ ⊢ₛₜ e : τ → ξ ++ Γ ⊢ₛₜ e : τ.
Proof. intros H1 H2. erewrite <- H1. by eapply context_weakening. Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma ren_upn_ren n m:
  (λ x : type, x.[ren (+1)].[upn (S n) (ren (+m))]) =
  (λ x : type, x.[upn n (ren (+m))].[ren (+1)]).
Proof.
  extensionality i.
  by asimpl.
Qed.

Lemma context_gen_rename Γ e τ n m :
  Γ ⊢ₛₜ e : τ → subst (upn n (ren (+m))) <$> Γ ⊢ₛₜ
                     e : τ.[upn n (ren (+m))].
Proof.
  intros Ht. revert n m.
  induction Ht => n m; try (asimpl in *; eauto using typed; fail).
  - econstructor.
    by rewrite list_lookup_fmap H.
  - destruct op; asimpl; econstructor; eauto.
  (* - asimpl. econstructor. *)
  (*   specialize (IHHt (S n) m). *)
  (*   asimpl in *. *)
  (*   rewrite -list_fmap_compose /compose in IHHt. *)
  (*   rewrite -list_fmap_compose /compose. *)
  (*   by rewrite -ren_upn_ren. *)
  (* - specialize (IHHt n m). asimpl in IHHt. *)
  (*   replace (τ.[τ'/].[upn n (ren (+m))]) with *)
  (*   (τ.[upn (S n) (ren (+m))].[τ'.[upn n (ren (+m))]/]) by by asimpl. *)
  (*   by econstructor. *)
  - specialize (IHHt n m). asimpl in IHHt.
    econstructor.
    by asimpl in *.
  - specialize (IHHt n m). asimpl in IHHt.
    replace (τ.[TRec τ/].[upn n (ren (+m))]) with
    (τ.[upn (S n) (ren (+m))].[TRec τ.[upn (S n) (ren (+m))]/]) by by asimpl.
    by econstructor.
  - specialize (IHHt (S n) m). asimpl in IHHt.
    econstructor. asimpl.
    rewrite -list_fmap_compose /compose in IHHt.
    rewrite -list_fmap_compose /compose.
    by rewrite -ren_upn_ren.
Qed.

Lemma context_rename Γ e τ m :
  Γ ⊢ₛₜ e : τ → subst (ren (+m)) <$> Γ ⊢ₛₜ e : τ.[ren (+m)].
Proof.
  eapply (context_gen_rename _ _ _ 0).
Qed.

Lemma typed_gen_subst Γ1 Γ2 e1 τ1 e2 τ2 :
  Γ1 ++ τ2 :: Γ2 ⊢ₛₜ e1 : τ1 →
  Γ2 ⊢ₛₜ e2 : τ2 →
  Γ1 ++ Γ2 ⊢ₛₜ e1.[upn (length Γ1) (e2 .: ids)] : τ1.
Proof.
  remember (Γ1 ++ τ2 :: Γ2) as ξ. intros Ht. revert Γ1 Γ2 e2 τ2 Heqξ.
  induction Ht => Γ1 Γ2 oe2 oτ2 Heqξ; asimpl in *; eauto using typed.
  - subst. rewrite iter_up; destruct lt_dec as [Hl | Hl].
    + econstructor.
      match goal with
        H : _ !! _ = Some _ |- _ => revert H
      end.
      rewrite !lookup_app_l; auto.
    + asimpl. remember (x - length Γ1) as n. destruct n.
       * match goal with
           H : (Γ1 ++ oτ2 :: Γ2) !! x = Some τ |- _ =>
           rewrite lookup_app_r in H; auto with lia; rewrite -Heqn in H;
             inversion H; subst
         end.
         by apply context_weakening.
       * asimpl.
         match goal with
           H : (Γ1 ++ oτ2 :: Γ2) !! x = Some τ |- _ =>
           rewrite lookup_app_r in H; auto with lia; rewrite -Heqn in H;
             inversion H; subst
         end.
         change (ids (length Γ1 + n)) with (@ids expr _ n).[ren (+(length Γ1))].
         by apply context_weakening; constructor.
  - econstructor; eauto.
    + eapply (IHHt2 (_ :: _)); eauto; by simpl; f_equal.
    + eapply (IHHt3 (_ :: _)); eauto; by simpl; f_equal.
  - econstructor; eauto.
    eapply (IHHt1 (_ :: _)); eauto; by simpl; f_equal.
  - econstructor; eauto.
    eapply (IHHt (_ :: _)); eauto; by simpl; f_equal.
  (* - econstructor. eapply (IHHt (_ :: _ :: _)); eauto; by simpl; repeat f_equal. *)
  - constructor.
    specialize (IHHt
      (subst (ren (+1)) <$> Γ1) (subst (ren (+1)) <$> Γ2)).
    asimpl in *. rewrite ?map_length in IHHt.
    repeat rewrite fmap_app. eapply IHHt; eauto using context_rename.
    by rewrite Heqξ; repeat rewrite fmap_app.
  (* - econstructor; eauto. *)
  (*   specialize (IHHt *)
  (*     (subst (ren (+1)) <$> Γ1) (subst (ren (+1)) <$> Γ2)). *)
  (*   asimpl in *. rewrite ?map_length in IHHt. *)
  (*   repeat rewrite fmap_app. eapply IHHt; eauto using context_rename. *)
  (*   by rewrite Heqξ; repeat rewrite fmap_app. *)
Qed.

Lemma typed_subst Γ2 e1 τ1 e2 τ2 :
  τ2 :: Γ2 ⊢ₛₜ e1 : τ1 → Γ2 ⊢ₛₜ e2 : τ2 → Γ2 ⊢ₛₜ e1.[e2/] : τ1.
Proof. apply (typed_gen_subst []). Qed.
