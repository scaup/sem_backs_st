From st.lam Require Import types lang typing tactics.
From st.lam.lib Require Import omega fixlam.

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

From st Require Import lang.

Instance type_constructor_eq_dec : EqDecision type_constructor.
Proof. solve_decision. Defined.

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

Opaque Ω.

Lemma CaseTC_subst tc σ e : (CaseTC tc e).[σ] = CaseTC tc e.[σ].
Proof. destruct tc; by asimpl. Qed.

Lemma CaseTC_typed (tc : type_constructor) (e : expr) Γ (d : Γ ⊢ₙₒ e : TUniverse_unfolded) :
  Γ ⊢ₙₒ CaseTC tc e : type_constructor_branch tc.
Proof. destruct tc; repeat eapply Case_typed; (by constructor) || (by apply Ω_typed) || (try by eapply d). Qed.

Definition inject (tc : type_constructor) : val := LamV (Fold (InjTC tc %0))%Eₙₒ.

Definition inject_val tc v := FoldV (InjVTC tc v).

Lemma inject_Closed (tc : type_constructor) : Closed (of_val (inject tc)).
Proof. destruct tc; intro σ; asimpl; done. Qed.

Definition extract (tc : type_constructor) : val := LamV (CaseTC tc (Unfold %0))%Eₙₒ.

Lemma extract_Closed (tc : type_constructor) : Closed (of_val (extract tc)).
Proof. destruct tc; intro σ; asimpl; done. Qed.

Lemma inject_step tc e (v : val) : e = of_val v → lam_step (inject tc e) (inject_val tc v).
Proof.
  intro. rewrite H /inject /inject_val.
  assert (of_val (FoldV (InjVTC tc v)) = Fold (InjTC tc v)) as ->. destruct tc; by simpl.
  apply head_prim_step. simpl.
  assert (Fold (InjTC tc v) = (Fold (InjTC tc (Var 0)).[of_val v/])) as ->. destruct tc; by asimpl.
  auto_head_step.
Qed.

Lemma inject_step' tc (v : val) : lam_step (inject tc (of_val v)) (inject_val tc v).
Proof.
  apply head_prim_step. simpl. assert (Fold (InjVTC tc v) = (Fold (InjTC tc (Var 0)).[of_val v/])) as ->. destruct tc; by asimpl. auto_head_step.
Qed.

Lemma extract_step tc (v : val) : lam_step (extract tc (of_val v)) (CaseTC tc (Unfold v)).
Proof.
  apply head_prim_step. simpl. assert (CaseTC tc (Unfold v) = (CaseTC tc (Unfold (Var 0))).[of_val v/]) as ->. asimpl. destruct tc; by asimpl. auto_head_step.
Qed.

Lemma inject_typed (tc : type_constructor) Γ :
  Γ ⊢ₙₒ inject tc : type_constructor_branch tc ⟶ TUniverse.
Proof. by apply Lam_typed, Fold_typed, InjTC_typed, Var_typed. Qed.

Lemma extract_typed (tc : type_constructor) Γ :
  Γ ⊢ₙₒ extract tc : TUniverse ⟶ type_constructor_branch tc.
Proof. by apply Lam_typed, CaseTC_typed, Unfold_typed, Var_typed. Qed.

Typeclasses Opaque TUniverse_body.
Global Opaque TUniverse_body.
Typeclasses Opaque TUniverse.
Global Opaque TUniverse.
Typeclasses Opaque TUniverse_unfolded.
Global Opaque TUniverse_unfolded.

Typeclasses Opaque inject.
Global Opaque inject.
Typeclasses Opaque extract.
Global Opaque extract.
