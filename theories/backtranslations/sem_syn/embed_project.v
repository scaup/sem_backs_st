From st.prelude Require Import autosubst.
From st.lam Require Import types lang typing tactics.
From st.lam.lib Require Import fixlam omega.
From st.backtranslations.un_syn Require Import universe.base.

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

Definition fixgenTRec (eb pb : val) : val :=
  (LamV (* 1 → ((τ → U) × (U → τ)) *) (
       LamV (* 1 *) (
           ( LamV (inject TCRec (Fold (eb.{ren (+2)} (Unfold %0)))) , (* τ → U *)
             LamV (Fold (pb.{ren (+2)} (Unfold (extract TCRec %0)))) (* U → τ *)
           )
         )
     )
  )%Eₙₒ.

Lemma fixgenTRec_subst (eb pb : val) (σ : var → expr) : (fixgenTRec eb pb).{σ} = fixgenTRec eb.{up σ} pb.{up σ}.
Proof. rewrite /fixgenTRec. simpl. rewrite inject_Closed extract_Closed. repeat rewrite -val_subst_valid. by asimpl. Qed.

Lemma fixgenTRec_typed (eb pb : val) Γ τb
      (peb : (TUnit ⟶ ((TRec τb ⟶ TUniverse) × (TUniverse ⟶ TRec τb)))%Tₙₒ :: Γ ⊢ₙₒ eb : τb.[TRec τb/] ⟶ TUniverse)
      (ppb : (TUnit ⟶ ((TRec τb ⟶ TUniverse) × (TUniverse ⟶ TRec τb)))%Tₙₒ :: Γ ⊢ₙₒ pb : TUniverse ⟶ τb.[TRec τb/]) :
  Γ ⊢ₙₒ fixgenTRec eb pb :
    (TUnit ⟶ ((TRec τb ⟶ TUniverse) × (TUniverse ⟶ TRec τb))) ⟶ (TUnit ⟶ ((TRec τb ⟶ TUniverse) × (TUniverse ⟶ TRec τb))).
Proof.
  assert (TUniverse = TUniverse.[TRec TUniverse/]) as eq; first by asimpl.
  constructor. constructor. constructor. constructor. apply App_typed with (τ1 := TRec TUniverse). apply inject_typed.
  constructor. apply App_typed with (τ1 := τb.[TRec τb/]).
  change (TRec τb :: TUnit :: (TUnit ⟶ (TRec τb ⟶ TUniverse) × (TUniverse ⟶ TRec τb))%Tₙₒ :: Γ) with
      ([TRec τb ; TUnit] ++ ((TUnit ⟶ (TRec τb ⟶ TUniverse) × (TUniverse ⟶ TRec τb))%Tₙₒ :: Γ)).
  rewrite -val_subst_valid. apply context_weakening. rewrite -eq. apply peb.
  constructor. by constructor.
  constructor. constructor. apply App_typed with (τ1 := TUniverse).
  change (TUniverse :: TUnit :: (TUnit ⟶ (TRec τb ⟶ TUniverse) × (TUniverse ⟶ TRec τb))%Tₙₒ :: Γ) with
      ([TUniverse ; TUnit] ++ ((TUnit ⟶ (TRec τb ⟶ TUniverse) × (TUniverse ⟶ TRec τb))%Tₙₒ :: Γ)).
  rewrite -val_subst_valid. apply context_weakening. apply ppb.
  rewrite eq. constructor. apply App_typed with (τ1 := TUniverse).
  apply extract_typed. rewrite -eq. by constructor.
Qed.

Global Opaque fixgenTRec.

Fixpoint ep_pair (dir : direction) (τ : type) : val :=
  (match τ with
   | TUnit => match dir with
             | Embed => inject TCUnit
             | Project => extract TCUnit
             end
   | TBool => match dir with
             | Embed => inject TCBool
             | downward => extract TCBool
             end
   | TInt => match dir with
            | Embed => inject TCInt
            | Project => extract TCInt
            end
   | TProd τ1 τ2 => match dir with
                   | Embed => LamV (LetIn (Fst %0)
                                        (LetIn (Snd %1)
                                               (inject TCProd ((ep_pair Embed τ1).{ren (+3)} %1, (ep_pair Embed τ2).{ren (+3)} %0))))
                   | Project => LamV (LetIn (extract TCProd %0)
                                          (LetIn (Fst %0)
                                                 (LetIn (Snd %1)
                                                        ((ep_pair Project τ1).{ren (+4)} %1 , (ep_pair Project τ2).{ren (+4)} %0))))
     end
   | TSum τ1 τ2 => match dir with
                  | Embed => LamV (Case %0
                                      (inject TCSum (InjL ((ep_pair Embed τ1).{ren (+2)} %0)))
                                      (inject TCSum (InjR ((ep_pair Embed τ2).{ren (+2)} %0))))
                  | Project => LamV (Case (extract TCSum %0)
                                        (InjL ((ep_pair Project τ1).{ren (+2)} %0))
                                        (InjR ((ep_pair Project τ2).{ren (+2)} %0)))
                  end
   | TArrow τ1 τ2 => match dir with
                    | Embed => LamV (inject TCArrow (Lam ((ep_pair Embed τ2).{ren (+2)} (%1 ((ep_pair Project τ1).{ren (+2)} %0)))))
                    | Project => LamV (Lam ((ep_pair Project τ2).{ren (+2)} (extract TCArrow %1 ((ep_pair Embed τ1).{ren (+2)} %0))))
                    end
   | TRec τb => let β := fixgenTRec (ep_pair Embed τb) (ep_pair Project τb) in
               LamV (FstSnd dir (LamV (FixArrow β.{ren (+2)} %0(*_*)) ()) %0)
   | TVar X => LamV (FstSnd dir (Var (S X) ()) %0)
  end)%Eₙₒ.

Definition direction_type dir τ :=
  match dir with
  | Embed => TArrow τ TUniverse
  | Project => TArrow TUniverse τ
  end.

Lemma ep_pair_typed_gen (τ : type) (τs : list type) (pτn : Closed_n (length τs) τ) (dir : direction) :
  map (fun τ => (TUnit ⟶ (τ ⟶ TUniverse) × (TUniverse ⟶ τ))%Tₙₒ) τs ⊢ₙₒ (ep_pair dir τ) : (direction_type dir τ.[subst_list τs]).
Proof.
  generalize dependent dir.
  generalize dependent τs.
  induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τb IHτb | X ];
    intros τs Cnτ dir; try by (destruct dir; (apply inject_typed || apply extract_typed)).
  - (* TProd *) destruct dir.
    + repeat ((rewrite -val_subst_valid; apply context_weakening3) || apply IHτ1 with (dir := Embed) || apply IHτ2 with (dir := Embed) || closed_solver || apply inject_typed || econstructor).
    + repeat ((rewrite -val_subst_valid; apply context_weakening4) || apply IHτ1 with (dir := Project) || apply IHτ2 with (dir := Project) || closed_solver || apply extract_typed || econstructor).
  - (* TSum *) destruct dir.
    + repeat ((rewrite -val_subst_valid; apply context_weakening2) || apply IHτ1 with (dir := Embed) || apply IHτ2 with (dir := Embed) || closed_solver || apply inject_typed || econstructor).
    + repeat ((rewrite -val_subst_valid; apply context_weakening2) || apply IHτ1 with (dir := Project) || apply IHτ2 with (dir := Project) || closed_solver || apply (extract_typed TCSum) || econstructor).
  - (* TArrow *) destruct dir.
    + repeat ((rewrite -val_subst_valid; apply context_weakening2) || apply IHτ1 with (dir := Project) || apply IHτ2 with (dir := Embed) || closed_solver || apply inject_typed || econstructor).
    + repeat ((rewrite -val_subst_valid; apply context_weakening2) || apply IHτ1 with (dir := Embed) || apply IHτ2 with (dir := Project) || closed_solver || apply (extract_typed TCArrow) || econstructor).
  - (* TRec *) destruct dir.
    + constructor. fold ep_pair.
      apply App_typed with (τ1 := (TRec τb).[subst_list τs]). 2: by constructor.
      apply Fst_typed with (τ2 := (TUniverse ⟶ (TRec τb).[subst_list τs])%Tₙₒ).
      apply App_typed with (τ1 := TUnit). 2: by constructor. apply Lam_typed.
      apply App_typed with (τ1 := TUnit). 2: by constructor.
      apply FixArrow_typed.
      rewrite -val_subst_valid. apply context_weakening2.
      apply fixgenTRec_typed.
      * asimpl. change (TRec τb.[up (subst_list τs)] .: subst_list τs) with (subst_list (TRec τb.[up (subst_list τs)] :: τs)).
        rewrite -map_cons. apply IHτb with (dir := Embed). closed_solver.
      * asimpl. change (TRec τb.[up (subst_list τs)] .: subst_list τs) with (subst_list (TRec τb.[up (subst_list τs)] :: τs)).
        rewrite -map_cons. apply IHτb with (dir := Project). closed_solver.
    + constructor. fold ep_pair.
      apply App_typed with (τ1 := TUniverse). 2: by constructor.
      apply Snd_typed with (τ1 := ((TRec τb).[subst_list τs] ⟶ TUniverse)%Tₙₒ).
      apply App_typed with (τ1 := TUnit). 2: by constructor. apply Lam_typed.
      apply App_typed with (τ1 := TUnit). 2: by constructor.
      apply FixArrow_typed.
      rewrite -val_subst_valid. apply context_weakening2.
      apply fixgenTRec_typed.
      * asimpl. change (TRec τb.[up (subst_list τs)] .: subst_list τs) with (subst_list (TRec τb.[up (subst_list τs)] :: τs)).
        rewrite -map_cons. apply IHτb with (dir := Embed). closed_solver.
      * asimpl. change (TRec τb.[up (subst_list τs)] .: subst_list τs) with (subst_list (TRec τb.[up (subst_list τs)] :: τs)).
        rewrite -map_cons. apply IHτb with (dir := Project). closed_solver.
  - (* TVar *)
    destruct (TVar_subst_list_closed_n_length _ _ Cnτ) as [τ [eq ->]].
    destruct dir; repeat econstructor; simpl; by rewrite list_lookup_fmap eq /=.
Qed.

Lemma ep_pair_typed (τ : type) (pτ : Closed τ) dir :
  [] ⊢ₙₒ (ep_pair dir τ) : (direction_type dir τ).
Proof. cut (fmap (fun τ => (TUnit ⟶ (τ ⟶ TUniverse) × (TUniverse ⟶ τ))%Tₙₒ) [] ⊢ₙₒ ep_pair dir τ : direction_type dir τ.[subst_list []]). by asimpl. by apply ep_pair_typed_gen. Qed.

Lemma ep_pair_Closed (τ : type) (pτ : Closed τ) dir :
  Closed (of_val $ ep_pair dir τ).
Proof.
  intro σ. replace (of_val $ ep_pair dir τ) with (of_val $ ep_pair dir τ).[ids] at 2 by by asimpl.
  erewrite (typed_subst_invariant [] _ _ σ ids). auto. apply ep_pair_typed.
  auto. simpl. lia.
Qed.
