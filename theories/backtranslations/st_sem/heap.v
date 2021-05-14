From st.lam Require Import lang tactics lib.fixlam.

Fixpoint encode_help (vs : list val) : val :=
  match vs with
  | nil => ()%Vₙₒ
  | cons v tl => (v, (encode_help tl))%Vₙₒ
  end.

Definition encode vs : val := (encode_help (reverse vs), length vs)%Vₙₒ(*heap*).

Lemma example (v1 v2 v3 v4 : val) : encode [v1; v2; v3; v4] = ((v4, (v3, (v2, (v1, ())))), 4)%Vₙₒ.
Proof. rewrite /encode. simpl. done. Qed.

Ltac rtc_step := eapply rtc_l; first auto_lam_step; simplify_custom.

(* allocation *)

Definition alloc_help (h : expr) (v : expr) : expr (* alloc_help h v : H *) :=
  ((v, Fst h), (Snd h + 1))%Eₙₒ.

Definition alloc : val (* : τ → H → H × nat *) :=
  LamV (*v*) (
      Lam (*h*) (
          (alloc_help %0 %1, (Snd %0))
        )
    )%Eₙₒ.

Definition alloc_v (v : val) : val (* : H → H × nat *) :=
  LamV (*h*) (
      (alloc_help %0 v.{ren (+1)}, (Snd %0))
    )%Eₙₒ.

Lemma alloc_help_spec (vs : list val) (v : val) :
  rtc lam_step (alloc_help (encode vs) v) (encode (vs ++ [v])).
Proof.
  auto_rtc_lam_step. auto_rtc_lam_step.
  rewrite reverse_snoc app_length /=.
  auto_rtc_lam_step. assert ((length vs + 1%nat)%Z = S (length vs)) as ->; first lia. apply rtc_refl.
Qed.

Lemma alloc_step (v : val) : lam_step (alloc v) (alloc_v v).
Proof.
  rewrite /alloc /alloc_v.
  assert (of_val $ LamV (alloc_help %0 v.{ren (+1)}, Snd %0)%Eₙₒ =
          (Lam (alloc_help %0 %1, Snd %0)%Eₙₒ).[of_val v/]
          ) as ->. rewrite -val_subst_valid. asimpl. done.
  apply head_prim_step. eapply App_Lam_head_step. by rewrite to_of_val.
Qed.

Lemma alloc_v_steps (vs : list val) (v : val) :
  rtc lam_step
      (alloc_v v (encode vs))
      (encode (vs ++ [v]), length vs)%Eₙₒ.
Proof.
  (* Local Opaque encode. *)
  do 1 rtc_step.
  eapply rtc_transitive.
  apply (rtc_lam_step_ctx (fill [PairLCtx _])).
  rewrite -val_subst_valid. asimpl.
  apply alloc_help_spec. simpl.
  change ((encode_help (reverse (vs ++ [v])), length (vs ++ [v]))%Eₙₒ) with
      (of_val (encode_help (reverse (vs ++ [v])), length (vs ++ [v]))%Vₙₒ).
  apply (rtc_lam_step_ctx (fill [PairRCtx _])).
  rtc_step. apply rtc_refl.
Qed.

Lemma alloc_steps (vs : list val) (v : val) :
  rtc lam_step
      (alloc v (encode vs))
      (encode (vs ++ [v]), length vs)%Eₙₒ.
Proof.
  (* apply rtc_l with (y := alloc_v v (encode vs)). *)
  (* apply head_prim_step. simpl. apply App_Lam_head_step. *)
  (* Local Opaque encode. *)
  do 2 rtc_step.
  eapply rtc_transitive.
  apply (rtc_lam_step_ctx (fill [PairLCtx _])).
  apply alloc_help_spec. simpl.
  change ((encode_help (reverse (vs ++ [v])), length (vs ++ [v]))%Eₙₒ) with
      (of_val (encode_help (reverse (vs ++ [v])), length (vs ++ [v]))%Vₙₒ).
  apply (rtc_lam_step_ctx (fill [PairRCtx _])).
  rtc_step. apply rtc_refl.
Qed.

(* reading *)

Definition read_help (h : expr) (i : expr) : expr (* read_help h i : # *) :=
  (Rec (*rec : h : H, H → # *) (
       LetIn (Fst %0)(*prod*) (
               LetIn (Snd %1)(*length*) (
                       If ((1 + i(*index*)) = %0)
                          (Fst %1(*prod*))
                          (* (Lam (%3(*rec*) %0) (Snd %1(*prod*), (%0(*length*) - 1))) *)
                          (%3(*rec*) (Snd %1(*prod*), (%0(*length*) - 1)))
                     )
             )
     ) h
  )%Eₙₒ.

Definition read : val (* nat → H → H × τ*) :=
  LamV (*i*) (
      Lam (* h *)
         (%0 , read_help %0 %5)
    )%Eₙₒ.

Definition read_i (i : nat) : val (* : H → H × nat *) :=
  LamV (*h*) (%0 , read_help %0 i)%Eₙₒ.

Lemma read_help_spec (vs : list val) (i : nat) (v : val) (piv : vs !! i = Some v) :
  rtc lam_step (read_help (encode vs) i)%Eₙₒ (v)%Eₙₒ.
Proof.
  induction vs as [|last vs IHvs] using rev_ind; try by (exfalso; inversion piv).
  eapply rtc_transitive. eapply nsteps_rtc. eapply App_Rec_nsteps. by rewrite to_of_val. simplify_custom.
  do 6 rtc_step;
  rewrite reverse_snoc; simpl.
  (* destruct (decide ((1%nat + i)%Z = S (length vs))) as [eq | neq]. *)
  + (* is equal *)
    (* rewrite bool_decide_eq_true_2; try done. *)
    repeat rtc_step.
    rewrite (list_lookup_middle vs [] last i) in piv; try by lia. inversion piv; try by lia.
    auto_rtc_lam_step.
    rewrite app_length /= in H. lia.
  + (* inductive case *)
    rewrite app_length /=. rtc_step.
    assert (i < length (vs ++ [last])). by eapply lookup_lt_Some. rewrite app_length /= in H. rewrite lookup_app_l in piv; try lia. specialize (IHvs piv).
    eapply rtc_l. apply (lam_step_ctx (fill [AppRCtx _])). auto_lam_step. simplify_custom.
    eapply rtc_l. apply (lam_step_ctx (fill [AppRCtx _])). auto_lam_step. simplify_custom.
    assert (S (length vs) - 1%nat = length vs)%Z as ->; try lia.
    apply IHvs. rewrite app_length /= in H0. lia.
Qed.

Lemma read_steps (vs : list val) (v : val) (i : nat) (H : vs !! i = Some v) :
  rtc lam_step
      (read i (encode vs))
      (encode vs, v)%Eₙₒ.
Proof.
  do 2 rtc_step.
  change ((encode_help (reverse vs), length vs)%Eₙₒ) with
      (of_val (encode_help (reverse vs), length vs)%Vₙₒ).
  apply (rtc_lam_step_ctx (fill [PairRCtx _])).
  by apply read_help_spec.
Qed.

Lemma read_i_steps (vs : list val) (v : val) (i : nat) (H : vs !! i = Some v) :
  rtc lam_step (read_i i (encode vs)) (encode vs, v)%Vₙₒ.
Proof.
  simpl.
  rtc_step.
  change ((encode_help (reverse vs), length vs)%Eₙₒ) with
      (of_val (encode_help (reverse vs), length vs)%Vₙₒ).
  apply (rtc_lam_step_ctx (fill [PairRCtx _])).
  by apply read_help_spec.
Qed.

Lemma read_step (i : nat) : lam_step (read i) (read_i i).
Proof. auto_lam_step. Qed.

(* writing *)

Definition write_help (h : expr) (i : expr) (v : expr) : expr (* read_help_list' h i v : nested_cart_product *) :=
  (Rec (*rec : h : H, H → P *) (
       LetIn (Fst %0)(*prod*) (
               LetIn (Snd %1)(*length*) (
                       If ((1 + i(*index*)) = %0)
                          (v.[ren (+4)], Snd %1(*prod*))
                          (Fst %1, %3(*rec*) (Snd %1(*prod*), (%0(*length*) - 1)))
                     )
             )
     ) h
  )%Eₙₒ.

Definition write : val (* : nat → τ → H → H × 1 *) :=
  LamV (*i*)
      (Lam (*v*) (
          Lam (* h *)
            ((write_help %0 %6 %1, (Snd %0)), ())
        ))%Eₙₒ.

Definition write_i (i : nat) : val (* : H → H × nat *) :=
  LamV (*v*) (Lam (* h *)
               ((write_help %0 i %1, (Snd %0)), ()))%Eₙₒ.

Definition write_i_v (i : nat) (v : val) : val (* : H → H × nat *) :=
  LamV (* h *) (((write_help %0 i v.{ren (+1)}), (Snd %0)), ())%Eₙₒ.


Lemma write_help_spec (vs : list val) (i : nat) (v v' : val) (piv : vs !! i = Some v) :
  rtc lam_step (write_help (encode vs) i v')%Eₙₒ (encode_help (reverse (<[i := v']> vs)))%Eₙₒ.
Proof.
  induction vs as [|last vs IHvs] using rev_ind; try by (exfalso; inversion piv).
  rewrite /encode reverse_snoc. simpl.
  eapply rtc_transitive. eapply nsteps_rtc. eapply App_Rec_nsteps. simpl. by rewrite !to_of_val /=. do 6 rtc_step.
  + (* is equal *) repeat rtc_step.
    rewrite app_length /= in H.
    rewrite (list_lookup_middle vs [] last i) in piv; try by lia. inversion piv.
    assert (i = length vs + 0) as ->; first lia. rewrite insert_app_r /= reverse_snoc. apply rtc_refl.
  + (* inductive case *)
    assert (i ≠ length vs). rewrite app_length /= in H. lia.
    assert (i < length (vs ++ [last])). by eapply lookup_lt_Some.
    assert (i < length vs). rewrite app_length /= in H1. lia.
    do 4 rtc_step.
    rewrite lookup_app_l in piv; try lia. specialize (IHvs piv).
    rewrite (insert_app_l vs [last] i ) /=; try lia. rewrite reverse_snoc /=.
    apply (rtc_lam_step_ctx (fill [PairRCtx _])).
    rewrite app_length /=.
    assert ((length vs + 1)%nat - 1%nat = length vs)%Z as ->; try lia. apply IHvs.
Qed.

Lemma write_steps (i : nat) (vs : list val) (v v' : val) (piv : vs !! i = Some v) :
  rtc lam_step
      (write i v' (encode vs))
      (encode (<[i := v']> vs), ())%Eₙₒ.
Proof.
  do 3 rtc_step.
  apply (rtc_lam_step_ctx (fill [PairLCtx _])).
  rewrite insert_length.
  eapply rtc_transitive.
  apply (rtc_lam_step_ctx (fill [PairLCtx _])).
  rewrite Rec_subst. asimpl.
  eapply write_help_spec. done.
  simpl. rtc_step. apply rtc_refl.
Qed.

Lemma write_step (i : nat) : lam_step (write i) (write_i i).
Proof. auto_lam_step. Qed.

Lemma write_i_step (i : nat) (v : val) : lam_step (write_i i v) (write_i_v i v).
Proof.
  rewrite /write_i /write_i_v.
  asimpl.
  rewrite /write_help. rewrite -val_subst_valid. asimpl.
  assert ((Lam
             (Rec
                (LetIn (Fst %0)
                       (LetIn (Snd %1)
                              (If (1 + i = %0) ((of_val v).[ren (+5)], Snd %1) (Fst %1, %3 (Snd %1, %0 - 1))))) %0, Snd %0, ())%Eₙₒ) =
          (Lam
             (Rec
                (LetIn (Fst (ids 0))
                       (LetIn (Snd (ids 1))
                              (If (1 + i = ids 0) (ids 5, Snd (ids 1))
                                  (Fst (ids 1), Var 3 (Snd (ids 1), ids 0 - 1))))) 
                (ids 0), Snd (ids 0), ())%Eₙₒ)%Eₙₒ.[of_val v/]
         ) as ->. asimpl. rewrite Rec_subst. asimpl. auto.
  apply head_prim_step. eapply App_Lam_head_step. by rewrite to_of_val.
Qed.

Lemma write_i_v_steps (vs : list val) (i : nat) (v v' : val) (piv : vs !! i = Some v) :
  rtc lam_step (write_i_v i v' (encode vs)) (encode (<[i := v']> vs), ())%Vₙₒ.
Proof.
  rtc_step.
  apply (rtc_lam_step_ctx (fill [PairLCtx _])).
  rewrite insert_length.
  eapply rtc_transitive.
  apply (rtc_lam_step_ctx (fill [PairLCtx _])).
  rewrite Rec_subst. rewrite -val_subst_valid. asimpl. 
  eapply write_help_spec. done.
  simpl. rtc_step. apply rtc_refl.
Qed.

(* monad *)

Definition retrn : val (* : τ → H → H × τ *):=
  LamV (
      Lam (
          (%0 , %1)
        )
    )%Eₙₒ.

Definition retrn_v (v : val) : val (* : τ → H → H × τ *):=
  LamV ((%0 , (of_val v).[ren (+1)]))%Eₙₒ.

Lemma retrn_step (v : val) : lam_step (retrn v) (retrn_v v).
Proof. apply head_prim_step. eapply App_Lam_head_step'. rewrite /retrn_v. by asimpl. by rewrite to_of_val. Qed.

Definition bind : val (* : (H → H × τ) → (τ → H → H × τ') → H → H × τ' *):=
  LamV (* a : H → H × τ *)(
      Lam (* f : τ → H → H × τ' *) (
          Lam (* h₀ : H *) (
              LetIn ((*a*)%2 (*h₀*)%0) (*h₁v*) (
                      LetIn (Fst %0(*h₁v*)) (*h₁*) (
                              LetIn (Snd %1) (*v*) (
                                      %4(*f*) %0(*v*) %1(*h₁*)
                                    )
                            )
                    )
            )
        )
    )%Eₙₒ.

Definition bind_v (v : val) : val (* : (τ → H → H × τ') → H → H × τ' *):=
  LamV (* f : τ → H → H × τ' *) (
      Lam (* h₀ : H *) (
          LetIn ((*a*)(of_val v).[ren (+2)] (*h₀*)%0) (*h₁v*) (
                  LetIn (Fst %0(*h₁v*)) (*h₁*) (
                          LetIn (Snd %1) (*v*) (
                                  %4(*f*) %0(*v*) %1(*h₁*)
                                )
                        )
                )
        )
    )%Eₙₒ.

Lemma bind_step (v : val) : lam_step (bind v) (bind_v v).
Proof. apply head_prim_step. eapply App_Lam_head_step'. rewrite /bind_v. by asimpl. by rewrite to_of_val. Qed.

Definition bind_v_f (v f : val) : val (* : H → H × τ' *):=
  LamV (* h₀ : H *) (
      LetIn ((*a*)(of_val v).[ren (+1)] (*h₀*)%0) (*h₁v*) (
              LetIn (Fst %0(*h₁v*)) (*h₁*) (
                      LetIn (Snd %1) (*v*) (
                              (of_val f).[ren (+4)](*f*) %0(*v*) %1(*h₁*)
                            )
                    )
            )
    )%Eₙₒ.

Lemma bind_v_step (v f : val) : lam_step (bind_v v f) (bind_v_f v f).
Proof. apply head_prim_step. eapply App_Lam_head_step'. rewrite /bind_v_f. by asimpl. by rewrite to_of_val. Qed.

Definition runst : val (* : (H → H × τ) → τ *):=
  LamV (* a : H → H × τ *)(
      Snd (%0 (encode []))
    )%Eₙₒ.

(* other *)

Lemma alloc_Closed σ : (of_val alloc).[σ] = alloc.
Proof. by asimpl. Qed.
Lemma read_Closed σ : (of_val read).[σ] = read.
Proof. by asimpl. Qed.
Lemma bind_Closed σ : (of_val bind).[σ] = bind.
Proof. by asimpl. Qed.
Lemma retrn_Closed σ : (of_val retrn).[σ] = retrn.
Proof. by asimpl. Qed.
Lemma runst_Closed σ : (of_val runst).[σ] = runst.
Proof. by asimpl. Qed.

Typeclasses Opaque alloc_help.
Global Opaque alloc_help.

Typeclasses Opaque read_help.
Global Opaque read_help.

Typeclasses Opaque write_help.
Global Opaque write_help.
