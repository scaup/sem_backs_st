From st.prelude Require Import autosubst.
From st.lam Require Import types lang typing tactics.
From st.lam.lib Require Import fixlam omega universe.base.

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

Definition fixgenTRecga (gb ab : val) : val :=
  (LamV (* 1 → ((τ → τ) × (τ → τ)) *) (
       LamV (* 1 *) (
           ( LamV (Fold (gb.{ren (+2)} (Unfold %0))) , (* τ → τ *)
             LamV (Fold (ab.{ren (+2)} (Unfold %0))) (* τ → τ *)
           )
         )
     )
  )%Eₙₒ.

Lemma fixgenTRecga_subst (gb ab : val) (σ : var → expr) : (fixgenTRecga gb ab).{σ} = fixgenTRecga gb.{up σ} ab.{up σ}.
Proof. rewrite /fixgenTRecga. repeat rewrite -val_subst_valid. by asimpl. Qed.

(* Lemma App_fixgenTRecga_lam_step (gb ab : val) (e : expr) : *)
(*   lam_step (fixgenTRecga gb ab (Lam e)) *)
(* ((LamV ( *)
(*            ( LamV (Fold ((of_val gb).[Lam e.[ren (0 .: (+3))] .: ren (+2)] (Unfold %0))) , (* τ → τ *) *)
(*              LamV (Fold ((of_val ab).[Lam e.[ren (0 .: (+3))] .: ren (+2)] (Unfold %0))) (* τ → τ *) *)
(*            ) *)
(*          )))%Eₙₒ. *)
(* Proof. *)
(*   assert ( *)
(* (of_val (LamV ( *)
(*            ( LamV (Fold ((of_val gb).[Lam e.[ren (0 .: (+3))] .: ren (+2)] (Unfold %0))) , (* τ → τ *) *)
(*              LamV (Fold ((of_val ab).[Lam e.[ren (0 .: (+3))] .: ren (+2)] (Unfold %0))) (* τ → τ *) *)
(*            ) *)
(*          )))%Eₙₒ = *)
(* ((LamV ( *)
(*            ( LamV (Fold ((of_val gb).[ren (+2)] (Unfold %0))) , (* τ → τ *) *)
(*              LamV (Fold ((of_val ab).[ren (+2)] (Unfold %0))) (* τ → τ *) *)
(*            ) *)
(*          )))%Eₙₒ.[Lam e/] *)
(*     ) as ->. by asimpl. *)
(*   apply head_prim_step. eapply App_Lam_head_step. by simpl. *)
(* Qed. *)

Lemma fixgenTRecga_typed (gb ab : val) Γ τb
      (pgb : (TUnit ⟶ ((TRec τb ⟶ TRec τb) × (TRec τb ⟶ TRec τb)))%Tₙₒ :: Γ ⊢ₙₒ gb : τb.[TRec τb/] ⟶ τb.[TRec τb/])
      (pab : (TUnit ⟶ ((TRec τb ⟶ TRec τb) × (TRec τb ⟶ TRec τb)))%Tₙₒ :: Γ ⊢ₙₒ ab : τb.[TRec τb/] ⟶ τb.[TRec τb/]) :
  Γ ⊢ₙₒ fixgenTRecga gb ab :
    (TUnit ⟶ ((TRec τb ⟶ TRec τb) × (TRec τb ⟶ TRec τb))) ⟶ (TUnit ⟶ ((TRec τb ⟶ TRec τb) × (TRec τb ⟶ TRec τb))).
Proof.
  constructor. constructor. constructor.
  constructor. constructor. apply App_typed with (τ1 := τb.[TRec τb/]). rewrite -val_subst_valid.
  apply context_weakening2. apply pgb.
  constructor. by constructor.
  constructor. constructor. apply App_typed with (τ1 := τb.[TRec τb/]). rewrite -val_subst_valid.
  apply context_weakening2. apply pab.
  constructor. by constructor.
Qed.

Global Opaque fixgenTRecga.

(* Lemma test (t : expr) : t = (ids 1).[up (ren (+2))]. *)
(* asimpl.  *)
Fixpoint ga_pair (ga : action) (τ : type) : val :=
  (match τ with
   | TUnit => match ga with
             | Guard => LamV %0
             | Assert => LamV (Seq %0 ())
             end
   | TBool => match ga with
             | Guard => LamV %0
             | Assert => LamV (If %0 true false)
             end
   | TInt => match ga with
            | Guard => LamV %0
            | Assert => LamV (%0 + 0)
            end
   | TProd τ1 τ2 => LamV (LetIn (Fst %0) (LetIn (Snd %1) ((ga_pair ga τ1).{ren (+3)} %1, (ga_pair ga τ2).{ren (+3)} %0)))
   | TSum τ1 τ2 => LamV (Case %0 (InjL ((ga_pair ga τ1).{ren (+2)} %0)) (InjR ((ga_pair ga τ2).{ren (+2)} %0)))
   | TArrow τ1 τ2 => LamV (Lam ((ga_pair ga τ2).{ren (+2)} (%1 ((ga_pair (opp_action ga) τ1).{ren (+2)} %0))))
   | TRec τb => let β := fixgenTRecga (ga_pair Guard τb) (ga_pair Assert τb) in
               LamV (FstSndga ga (LamV (FixArrow β.{ren (+2)} %0(*_*)) ()) %0)
   | TVar X => LamV (FstSndga ga (Var (S X) ()) %0)
   end)%Eₙₒ.

(* We never actually need typedness of ga; but it serves as a good sanity check *)
Lemma ga_typed_gen (τ : type) (τs : list type) (pτn : Closed_n (length τs) τ) (ga : action) :
  map (fun τ => (TUnit ⟶ (τ ⟶ τ) × (τ ⟶ τ))%Tₙₒ) τs ⊢ₙₒ (ga_pair ga τ) : (τ.[subst_list τs] ⟶ τ.[subst_list τs]).
Proof.
  generalize dependent ga.
  generalize dependent τs.
  induction τ as [ | | | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τ1 IHτ1 τ2 IHτ2 | τb IHτb | X ]; intros τs Cnτ ga;
    try by (destruct ga; by repeat econstructor).
  - repeat econstructor; fold ga_pair.
    rewrite -val_subst_valid. apply context_weakening3. apply IHτ1. closed_solver.
    rewrite -val_subst_valid. apply context_weakening3. apply IHτ2. closed_solver.
  - repeat econstructor; fold ga_pair.
    rewrite -val_subst_valid. apply context_weakening2. apply IHτ1. closed_solver.
    rewrite -val_subst_valid. apply context_weakening2. apply IHτ2. closed_solver.
  - repeat econstructor; fold ga_pair.
    rewrite -val_subst_valid. apply context_weakening2. apply IHτ2. closed_solver.
    rewrite -val_subst_valid. apply context_weakening2. apply IHτ1. closed_solver.
  - (* TRec *) destruct ga.
    + constructor. fold ga_pair.
      apply App_typed with (τ1 := (TRec τb).[subst_list τs]). 2: by constructor.
      eapply Fst_typed.
      apply App_typed with (τ1 := TUnit). 2: by constructor. apply Lam_typed.
      apply App_typed with (τ1 := TUnit). 2: by constructor.
      apply FixArrow_typed. rewrite -val_subst_valid. apply context_weakening2. apply fixgenTRecga_typed.
      * asimpl. change (TRec τb.[up (subst_list τs)] .: subst_list τs) with (subst_list (TRec τb.[up (subst_list τs)] :: τs)).
        rewrite -map_cons. apply IHτb with (ga := Guard). closed_solver.
      * asimpl. change (TRec τb.[up (subst_list τs)] .: subst_list τs) with (subst_list (TRec τb.[up (subst_list τs)] :: τs)).
        rewrite -map_cons. apply IHτb with (ga := Assert). closed_solver.
    + constructor. fold ga_pair.
      eapply App_typed. 2: by constructor.
      eapply Snd_typed.
      apply App_typed with (τ1 := TUnit). 2: by constructor. apply Lam_typed.
      apply App_typed with (τ1 := TUnit). 2: by constructor.
      apply FixArrow_typed. rewrite -val_subst_valid. apply context_weakening2.
      simpl. apply fixgenTRecga_typed.
      * asimpl. change (TRec τb.[up (subst_list τs)] .: subst_list τs) with (subst_list (TRec τb.[up (subst_list τs)] :: τs)).
        rewrite -map_cons. apply IHτb with (ga := Guard). closed_solver.
      * asimpl. change (TRec τb.[up (subst_list τs)] .: subst_list τs) with (subst_list (TRec τb.[up (subst_list τs)] :: τs)).
        rewrite -map_cons. apply IHτb with (ga := Assert). closed_solver.
  - (* TVar *)
    destruct (TVar_subst_list_closed_n_length _ _ Cnτ) as [τ [eq ->]].
    destruct ga; repeat econstructor; simpl; by rewrite list_lookup_fmap eq /=.
Qed.
