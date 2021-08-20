From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From iris_string_ident Require Import ltac2_string_ident.
From st.STLCmuVS Require Import lang wkpre tactics lib.fixarrow.
From st.backtranslations.st_sem Require Import ghost.
From st.backtranslations.st_sem.heap_emul Require Import base.
From st.prelude Require Import at_least_one.

Ltac rtc_step := eapply rtc_l; first auto_STLCmuVS_step; simplify_custom.

(* allocation *)

Lemma alloc_help_spec (vs : list val) (v : val) :
  rtc STLCmuVS_step (alloc_help (encode vs) v) (encode (vs ++ [v])).
Proof.
  auto_rtc_STLCmuVS_step. auto_rtc_STLCmuVS_step.
  rewrite reverse_snoc app_length /=.
  auto_rtc_STLCmuVS_step. assert ((length vs + 1%nat)%Z = S (length vs)) as ->; first lia. apply rtc_refl.
Qed.

Lemma alloc_v_steps (vs : list val) (v : val) :
  rtc STLCmuVS_step
      (alloc_v v (encode vs))
      (encode (vs ++ [v]), length vs)%Eₙₒ.
Proof.
  rewrite /alloc_v.
  apply rtc_l with (y := (alloc_help (encode vs) v, Snd (encode vs))%Eₙₒ).
  apply head_prim_step. eapply App_Lam_head_step'. by asimpl. by rewrite to_of_val.
  eapply rtc_transitive.
  apply (rtc_STLCmuVS_step_ctx (fill [PairLCtx _])).
  apply alloc_help_spec. simpl.
  change ((encode_help (reverse (vs ++ [v])), length (vs ++ [v]))%Eₙₒ) with
      (of_val (encode_help (reverse (vs ++ [v])), length (vs ++ [v]))%Vₙₒ).
  apply (rtc_STLCmuVS_step_ctx (fill [PairRCtx _])).
  rtc_step. apply rtc_refl.
Qed.

Lemma alloc_step (v : val) : STLCmuVS_step (alloc v) (alloc_v v).
Proof.
  rewrite /alloc /alloc_v.
  apply head_prim_step. eapply App_Lam_head_step'. by asimpl. by rewrite to_of_val.
Qed.

(* reading *)

Lemma read_help_spec (vs : list val) (i : nat) (v : val) (piv : vs !! i = Some v) :
  rtc STLCmuVS_step (read_help (encode vs) i)%Eₙₒ (v)%Eₙₒ.
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
    auto_rtc_STLCmuVS_step.
    rewrite app_length /= in H. lia.
  + (* inductive case *)
    rewrite app_length /=. rtc_step.
    assert (i < length (vs ++ [last])). by eapply lookup_lt_Some. rewrite app_length /= in H. rewrite lookup_app_l in piv; try lia. specialize (IHvs piv).
    eapply rtc_l. apply (STLCmuVS_step_ctx (fill [AppRCtx _])). auto_STLCmuVS_step. simplify_custom.
    eapply rtc_l. apply (STLCmuVS_step_ctx (fill [AppRCtx _])). auto_STLCmuVS_step. simplify_custom.
    assert (S (length vs) - 1%nat = length vs)%Z as ->; try lia.
    apply IHvs. rewrite app_length /= in H0. lia.
Qed.

Lemma read_i_steps (vs : list val) (v : val) (i : nat) (H : vs !! i = Some v) :
  rtc STLCmuVS_step (read_i i (encode vs)) (encode vs, v)%Vₙₒ.
Proof.
  simpl.
  eapply rtc_l.
  auto_STLCmuVS_step. simplify_custom.
  change ((encode_help (reverse vs), length vs)%Eₙₒ) with
      (of_val (encode_help (reverse vs), length vs)%Vₙₒ).
  apply (rtc_STLCmuVS_step_ctx (fill [PairRCtx _])).
  by apply read_help_spec.
Qed.

Lemma read_i_at_least_one (vs : list val) (v : val) (i : nat) (H : vs !! i = Some v) :
  at_least_one STLCmuVS_step (read_i i (encode vs)) (encode vs, v)%Vₙₒ.
Proof.
  simpl.
  eapply at_least_one_l.
  auto_STLCmuVS_step. simplify_custom.
  change ((encode_help (reverse vs), length vs)%Eₙₒ) with
      (of_val (encode_help (reverse vs), length vs)%Vₙₒ).
  apply (rtc_STLCmuVS_step_ctx (fill [PairRCtx _])).
  by apply read_help_spec.
Qed.

Section wp_read_i.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG STLCmuVS_lang Σ}.
  Context `{ghost_mapG_inst : !ghost_mapG Σ nat (prod val val)}.

  Lemma wp_read_i Φ (vs : list val) (v : val) (i : nat) : ▷ (Φ (encode vs, v)%Vₙₒ ∗ ⌜ vs !! i = Some v ⌝) ⊢ WP read_i i (encode vs) ?{{Φ}}.
  Proof.
    iIntros "H". iApply wp_step_later.
    auto_STLCmuVS_step. simplify_custom.
    iNext. iDestruct "H" as "[H %H]".
    iApply wp_rtc_steps.
    change ((encode_help (reverse vs), length vs)%Eₙₒ) with
        (of_val (encode_help (reverse vs), length vs)%Vₙₒ).
    apply (rtc_STLCmuVS_step_ctx (fill [PairRCtx _])).
    by apply read_help_spec. simpl.
    change ((encode_help (reverse vs), length vs)%Eₙₒ) with
        (of_val (encode vs)%Vₙₒ).
    change ((encode vs, v)%Eₙₒ) with
        (of_val (encode vs, v)%Vₙₒ).
    by iApply wp_value'.
  Qed.

End wp_read_i.

Lemma read_step (i : nat) : STLCmuVS_step (read i) (read_i i).
Proof. apply head_prim_step. eapply App_Lam_head_step'. by asimpl. by simpl. Qed.

(* writing *)

Lemma write_help_spec (vs : list val) (i : nat) (v v' : val) (piv : vs !! i = Some v) :
  rtc STLCmuVS_step (write_help (encode vs) i v')%Eₙₒ (encode_help (reverse (<[i := v']> vs)))%Eₙₒ.
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
    apply (rtc_STLCmuVS_step_ctx (fill [PairRCtx _])).
    rewrite app_length /=.
    assert ((length vs + 1)%nat - 1%nat = length vs)%Z as ->; try lia. apply IHvs.
Qed.

Definition write_i_v_vs (i : expr) (v : expr) (vs : expr) : expr (* : H → H × nat *) :=
  (((write_help vs i v), (Snd vs)), ())%Eₙₒ.

Lemma write_i_v_step i v (vs : val) :
  STLCmuVS_step (write_i_v i v vs) (write_i_v_vs i v vs).
Proof.
  apply head_prim_step. eapply App_Lam_head_step'.
  asimpl. rewrite Rec_subst /write_i_v_vs /write_help. by asimpl. by rewrite to_of_val.
Qed.

Lemma write_i_v_steps (vs : list val) (i : nat) (v v' : val) (piv : vs !! i = Some v) :
  rtc STLCmuVS_step (write_i_v i v' (encode vs)) (encode (<[i := v']> vs), ())%Vₙₒ.
Proof.
  rtc_step.
  apply (rtc_STLCmuVS_step_ctx (fill [PairLCtx _])).
  rewrite insert_length.
  eapply rtc_transitive.
  apply (rtc_STLCmuVS_step_ctx (fill [PairLCtx _])).
  rewrite Rec_subst. asimpl.
  eapply write_help_spec. done.
  simpl. rtc_step. apply rtc_refl.
Qed.

Lemma write_i_v_vs_steps (vs : list val) (i : nat) (v v' : val) (piv : vs !! i = Some v) :
  rtc STLCmuVS_step (write_i_v_vs i v' (encode vs)) (encode (<[i := v']> vs), ())%Vₙₒ.
Proof.
  rewrite /write_i_v_vs.
  simpl.
  apply (rtc_STLCmuVS_step_ctx (fill [PairLCtx _])).
  rewrite insert_length.
  eapply rtc_transitive.
  apply (rtc_STLCmuVS_step_ctx (fill [PairLCtx _])).
  eapply write_help_spec. done.
  simpl. rtc_step. apply rtc_refl.
Qed.

Lemma write_i_v_at_least_one (vs : list val) (i : nat) (v v' : val) (piv : vs !! i = Some v) :
  at_least_one STLCmuVS_step (write_i_v i v' (encode vs)) (encode (<[i := v']> vs), ())%Vₙₒ.
Proof.
  eapply at_least_one_l. auto_STLCmuVS_step. simplify_custom.
  apply (rtc_STLCmuVS_step_ctx (fill [PairLCtx _])).
  rewrite insert_length.
  eapply rtc_transitive.
  apply (rtc_STLCmuVS_step_ctx (fill [PairLCtx _])).
  rewrite Rec_subst. asimpl.
  eapply write_help_spec. done.
  simpl. rtc_step. apply rtc_refl.
Qed.

Lemma write_i_step (i : val) (v : val) : STLCmuVS_step (write_i i v) (write_i_v i v).
Proof.
  rewrite /write_i.
  apply head_prim_step. eapply App_Lam_head_step'.
  asimpl. rewrite Rec_subst. asimpl. rewrite /write_help. by asimpl.
  by rewrite to_of_val.
Qed.

Lemma write_step (i : val) : STLCmuVS_step (write i) (write_i i).
Proof.
  rewrite /write.
  apply head_prim_step. eapply App_Lam_head_step'.
  asimpl. rewrite /write_help Rec_subst. asimpl. rewrite /write_help. by asimpl.
  by rewrite to_of_val.
Qed.

(* Section wp_write_i_v. *)

(*   Context `{Σ : !gFunctors}. *)
(*   Context `{irisG_inst : !irisG STLCmuVS_lang Σ}. *)
(*   Context `{ghost_mapG_inst : !ghost_mapG Σ nat (prod val val)}. *)

(*   Lemma wp_write_i_v γ Φ (ps : list (val * val)) (v1 v1' v2 v2' : val) (i : nat) : *)
(*     ⊢ auth_list γ ps -∗ ▷ i ↪[γ] (v1,v1') -∗ *)
(*       (auth_list γ (<[ i := (v2,v2') ]> ps) -∗ i ↪[γ] (v2,v2') -∗ Φ (encode (<[i := v2]> ps.*1), ())%Vₙₒ) -∗ *)
(*       WP write_i_v i v2 (encode ps.*1) {{Φ}}. *)
(*   Proof. *)
(*     iIntros "Hauth Hi Hu". iApply wp_step_later. auto_STLCmuVS_step. simplify_custom. iNext. *)

(*   apply (rtc_STLCmuVS_step_ctx (fill [PairLCtx _])). *)
(*   rewrite insert_length. *)
(*   eapply rtc_transitive. *)
(*   apply (rtc_STLCmuVS_step_ctx (fill [PairLCtx _])). *)
(*   rewrite Rec_subst. asimpl. *)
(*   eapply write_help_spec. done. *)
(*   simpl. rtc_step. apply rtc_refl. *)

(*     auto_STLCmuVS_step. simplify_custom. *)
(*     iNext. iDestruct "H" as "[H %H]". *)
(*     iApply wp_rtc_steps. *)
(*     change ((encode_help (reverse vs), length vs)%Eₙₒ) with *)
(*         (of_val (encode_help (reverse vs), length vs)%Vₙₒ). *)
(*     apply (rtc_STLCmuVS_step_ctx (fill [PairRCtx _])). *)
(*     by apply read_help_spec. simpl. *)
(*     change ((encode_help (reverse vs), length vs)%Eₙₒ) with *)
(*         (of_val (encode vs)%Vₙₒ). *)
(*     change ((encode vs, v)%Eₙₒ) with *)
(*         (of_val (encode vs, v)%Vₙₒ). *)
(*     by iApply wp_value'. *)
(*   Qed. *)

(* End wp_write_i_v. *)

(* monad *)

Lemma retrn_step (v : val) : STLCmuVS_step (retrn v) (retrn_v v).
Proof. apply head_prim_step. eapply App_Lam_head_step'. rewrite /retrn_v. by asimpl. by rewrite to_of_val. Qed.

Definition bind_v_f (v f : expr) : val (* : H → H × τ' *):=
  LamV (* h₀ : H *) (
      LetIn ((*a*)v.[ren (+1)] (*h₀*)%0) (*h₁v*) (
              LetIn (Fst %0(*h₁v*)) (*h₁*) (
                      LetIn (Snd %1) (*v*) (
                              f.[ren (+4)](*f*) %0(*v*) %1(*h₁*)
                            )
                    )
            )
    )%Eₙₒ.


Lemma bind_step (v : val) : STLCmuVS_step (bind v) (bind_v v).
Proof. apply head_prim_step. eapply App_Lam_head_step'. by asimpl. by rewrite to_of_val. Qed.

Lemma bind_v_step (v f : val) : STLCmuVS_step (bind_v v f) (bind_v_f v f).
Proof. apply head_prim_step. eapply App_Lam_head_step'. by asimpl. by rewrite to_of_val. Qed.

Lemma bind_v_f_step (v r1 r2 s1 f h0 h1 h2 : STLCmuVS.lang.val) :
  rtc STLCmuVS_step (v h0) (h1, r1)%Eₙₒ →
  rtc STLCmuVS_step (f r1) s1 →
  rtc STLCmuVS_step (s1 h1) (h2, r2)%Eₙₒ →
  rtc STLCmuVS_step (bind_v_f v f h0) (h2, r2)%Eₙₒ.
Proof.
  intros H1 H2 H3.
  rewrite /bind_v_f.
  rtc_step.
  eapply rtc_transitive. by apply (rtc_STLCmuVS_step_ctx (fill_item (LetInCtx _))). simpl.
  do 5 rtc_step.
  eapply rtc_transitive. by apply (rtc_STLCmuVS_step_ctx (fill_item (AppLCtx _))). auto.
Qed.

(* other *)

Typeclasses Opaque alloc_help.
Global Opaque alloc_help.

Typeclasses Opaque read_help.
Global Opaque read_help.

Typeclasses Opaque write_help.
Global Opaque write_help.
