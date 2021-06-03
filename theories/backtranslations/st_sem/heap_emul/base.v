From st.lam Require Import lang tactics lib.fixlam.

Fixpoint encode_help (vs : list val) : val :=
  match vs with
  | nil => ()%Vₙₒ
  | cons v tl => (v, (encode_help tl))%Vₙₒ
  end.

Definition encode vs : val := (encode_help (reverse vs), length vs)%Vₙₒ(*heap*).

Lemma encode_empty_subst σ : (of_val $ encode []).[σ] = of_val (encode []).
Proof. by asimpl. Qed.

Lemma example (v1 v2 v3 v4 : val) : encode [v1; v2; v3; v4] = ((v4, (v3, (v2, (v1, ())))), 4)%Vₙₒ.
Proof. rewrite /encode. simpl. done. Qed.

(* allocation *)

Definition alloc_help (h : expr) (v : expr) : expr (* alloc_help h v : H *) :=
  ((v, Fst h), (Snd h + 1))%Eₙₒ.

Definition alloc_v (v : expr) : val (* : H → H × nat *) :=
  LamV (*h*) (
      (alloc_help %0 v.[ren (+1)], (Snd %0))
    )%Eₙₒ.

Definition alloc : val (* : τ → H → H × nat *) :=
  LamV (*v*) (
      alloc_v %0
    )%Eₙₒ.

(* reading *)

Definition read_help (h : expr) (i : expr) : expr (* read_help h i : # *) :=
  (Rec (*rec : h : H, H → # *) (
       LetIn (Fst %0)(*prod*) (
               LetIn (Snd %1)(*length*) (
                       If ((1 + i.[ren (+4)](*index*)) = %0)
                          (Fst %1(*prod*))
                          (* (Lam (%3(*rec*) %0) (Snd %1(*prod*), (%0(*length*) - 1))) *)
                          (%3(*rec*) (Snd %1(*prod*), (%0(*length*) - 1)))
                     )
             )
     ) h
  )%Eₙₒ.

Definition read_i (i : expr) : val (* : H → H × nat *) :=
  LamV (*h*) (%0 , read_help %0 i.[ren (+1)])%Eₙₒ.

Definition read : val (* nat → H → H × τ*) :=
  LamV (*i*) (
      read_i %0
    )%Eₙₒ.

(* writing *)

Definition write_help (h : expr) (i : expr) (v : expr) : expr (* read_help_list' h i v : nested_cart_product *) :=
  (Rec (*rec : h : H, H → P *) (
       LetIn (Fst %0)(*prod*) (
               LetIn (Snd %1)(*length*) (
                       If ((1 + i.[ren (+4)](*index*)) = %0)
                          (v.[ren (+4)], Snd %1(*prod*))
                          (Fst %1, %3(*rec*) (Snd %1(*prod*), (%0(*length*) - 1)))
                     )
             )
     ) h
  )%Eₙₒ.

Definition write_i_v (i : expr) (v : expr) : val (* : H → H × nat *) :=
  LamV (* h *) (((write_help %0 i.[ren (+1)] v.[ren (+1)]), (Snd %0)), ())%Eₙₒ.

Definition write_i (i : expr) : val (* : τ → H → H × nat *) :=
  LamV (*v*) (write_i_v i.[ren (+1)] %0)%Eₙₒ.

Definition write : val (* : nat → τ → H → H × 1 *) :=
  LamV (*i*) (write_i %0)%Eₙₒ.

(* monad *)

Definition retrn : val (* : τ → H → H × τ *):=
  LamV (
      Lam (
          (%0 , %1)
        )
    )%Eₙₒ.

Definition retrn_v (v : val) : val (* : τ → H → H × τ *):=
  LamV ((%0 , (of_val v).[ren (+1)]))%Eₙₒ.

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

Definition bind_v (v : expr) : val (* : (τ → H → H × τ') → H → H × τ' *):=
  LamV (* f : τ → H → H × τ' *) (bind_v_f v.[ren (+1)] %0)%Eₙₒ.

Definition bind : val (* : (H → H × τ) → (τ → H → H × τ') → H → H × τ' *):=
  LamV (* a : H → H × τ *)(bind_v %0)%Eₙₒ.

Lemma bind_step (v : val) : lam_step (bind v) (bind_v v).
Proof. apply head_prim_step. eapply App_Lam_head_step'. by asimpl. by rewrite to_of_val. Qed.

Lemma bind_v_step (v f : val) : lam_step (bind_v v f) (bind_v_f v f).
Proof. apply head_prim_step. eapply App_Lam_head_step'. by asimpl. by rewrite to_of_val. Qed.

Definition runst : val (* : (H → H × τ) → τ *):=
  LamV (* a : H → H × τ *)(
      Snd (%0 (encode []))
    )%Eₙₒ.

(* other *)

Lemma alloc_Closed σ : (of_val alloc).[σ] = alloc.
Proof. by asimpl. Qed.
Lemma write_Closed σ : (of_val write).[σ] = write.
Proof. by asimpl. Qed.
Lemma read_Closed σ : (of_val read).[σ] = read.
Proof. by asimpl. Qed.
Lemma bind_Closed σ : (of_val bind).[σ] = bind.
Proof. by asimpl. Qed.
Lemma retrn_Closed σ : (of_val retrn).[σ] = retrn.
Proof. by asimpl. Qed.
Lemma runst_Closed σ : (of_val runst).[σ] = runst.
Proof. by asimpl. Qed.
