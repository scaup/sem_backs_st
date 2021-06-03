From st.prelude Require Import autosubst generic.
From st.lam Require Import types.

Inductive nr_type :=
 | NRTUnit : nr_type
 | NRTBool : nr_type
 | NRTInt : nr_type
 | NRTProd (τ1 τ2 : nr_type) : nr_type
 | NRTSum (τ1 τ2 : nr_type) : nr_type
 | NRTArrow (τ1 τ2 : nr_type) : nr_type.

Global Instance type_eq_dec (τ τ' : nr_type) : Decision (τ = τ').
Proof. solve_decision. Defined.

Inductive nr_type_constructor :=
  | NRTCUnit
  | NRTCBool
  | NRTCInt
  | NRTCProd
  | NRTCSum
  | NRTCArrow
  | NRTCRec.

Fixpoint nr_type_type (τ : nr_type) : type :=
  match τ with
  | NRTUnit => TUnit
  | NRTBool => TBool
  | NRTInt => TInt
  | NRTProd τ1 τ2 => TProd (nr_type_type τ1) (nr_type_type τ2)
  | NRTSum τ1 τ2 => TSum (nr_type_type τ1) (nr_type_type τ2)
  | NRTArrow τ1 τ2 => TArrow (nr_type_type τ1) (nr_type_type τ2)
  end.

Coercion nr_type_type : nr_type >-> type.
