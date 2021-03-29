From st Require Export autosubst.

Inductive type :=
 | TUnit : type
 | TBool : type
 | TInt : type
 | TProd (τ1 τ2 : type) : type
 | TSum (τ1 τ2 : type) : type
 | TArrow (τ1 τ2 : type) : type
 | TRec (τ : {bind 1 of type})
 | TVar (X : var)
 | TForall (τ : {bind 1 of type}).

Global Instance type_eq_dec (τ τ' : type) : Decision (τ = τ').
Proof. solve_decision. Defined.

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Declare Scope types_nost_scope.

Infix "×" := TProd (at level 49) : types_no_st_scope.
Infix "+" := TSum : types_no_st_scope.
Infix "⟶" := TArrow (at level 51) : types_no_st_scope.

Delimit Scope types_no_st_scope with Tₙₒ.

Lemma test : (TProd (TVar 0) (TVar 1)).[TBool, TInt/] = TProd TBool TInt.
Proof. by simpl. Qed.

Lemma test' : (TProd (TVar 0) (TVar 1)).[TBool/].[TInt/] = TProd TBool TInt.
Proof. by simpl. Qed.

(* Lemma test'' : (TVar 0).[TVar 0/].[TInt/] = (TVar 0).[TVar 0,TInt/]. *)
(* Proof. simpl. Qed. *)
