From st.prelude Require Import autosubst generic.

Inductive type :=
 | TUnit : type
 | TBool : type
 | TInt : type
 | TProd (τ1 τ2 : type) : type
 | TSum (τ1 τ2 : type) : type
 | TArrow (τ1 τ2 : type) : type
 | TRec (τ : {bind 1 of type})
 | TVar (X : var).
 (* | TForall (τ : {bind 1 of type}). *)

Global Instance type_eq_dec (τ τ' : type) : Decision (τ = τ').
Proof. solve_decision. Defined.

Instance TVar_Inj : Inj eq eq TVar. intros x1 x2 eq. by inversion eq. Qed.

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Declare Scope types_no_st_scope.

Infix "×" := TProd (at level 49) : types_no_st_scope.
Infix "+" := TSum : types_no_st_scope.
Infix "⟶" := TArrow (at level 51,right associativity) : types_no_st_scope.

Delimit Scope types_no_st_scope with Tₙₒ.

Lemma TVar_subst_list_closed_n_length (τs : list type) (X : var) (p : Closed_n (length τs) (TVar X)) :
  (exists τ : type, τs !! X = Some τ ∧ (TVar X).[subst_list τs] = τ).
Proof.
  destruct (τs !! X) eqn:eq. exists t. split; auto. by apply ids_subst_list_lookup.
  assert (length τs ≤ X). by apply lookup_ge_None.
  assert (X < length τs). by apply ids_lt_Closed_n. lia.
Qed.

Inductive type_constructor :=
  | TCUnit
  | TCBool
  | TCInt
  | TCProd
  | TCSum
  | TCArrow
  | TCRec.
