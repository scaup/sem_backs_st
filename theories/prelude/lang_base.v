From st.prelude Require Export generic.

Inductive base_lit : Set :=
| LitInt (n : Z) | LitBool (b : bool) | LitUnit.

Inductive bin_op : Set :=
| PlusOp | MinusOp | LeOp | LtOp | EqOp.

