From st Require Export autosubst.

Inductive type :=
 | TUnit : type
 | TBool : type
 | TInt : type
 | TProd : type → type → type
 | TSum : type → type → type
 | TArrow : type → type → type
 | TRec (τ : {bind 1 of type})
 | TVar (X : var)
 | TForall (τ : {bind 1 of type})
 | TSTref (ρ τ : type)
 | TST (ρ τ : type).

Global Instance type_eq_dec (τ τ' : type) : Decision (τ = τ').
Proof. solve_decision. Defined.

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Declare Scope types_nost_scope.

Infix "×" := TProd (at level 99) : types_st_scope.
Infix "+" := TSum : types_st_scope.
Infix "⟶" := TArrow (at level 100) : types_st_scope.

Delimit Scope types_st_scope with Tₛₜ.
