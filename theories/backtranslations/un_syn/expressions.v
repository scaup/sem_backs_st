From st.lam Require Import lang types.
From st.backtranslations.un_syn Require Import universe.base.

Reserved Notation "<< e >>" (at level 4, e at next level).
Fixpoint back_expr (e : expr) : expr :=
  match e with
  | Var x => x
  | LetIn e1 e2 => LetIn <<e1>> <<e2>>
  | Lam e => inject TCArrow (Lam <<e>>)
  (* | Fix e => Fix (extract TCArrow <<e>>) *)
  | App e1 e2 => extract TCArrow <<e1>> <<e2>>
  | Lit l => match l with
            | LitInt n => inject TCInt n
            | LitBool b => inject TCBool b
            | LitUnit => inject TCUnit LitUnit
            end
  | BinOp op e1 e2 => inject (match op with
                             | PlusOp => TCInt
                             | MinusOp => TCInt
                             | LeOp => TCBool
                             | LtOp => TCBool
                             | EqOp => TCBool
                             end) (BinOp op (extract TCInt <<e1>>) (extract TCInt <<e2>>))
  | If e0 e1 e2 => If (extract TCBool <<e0>>) <<e1>> <<e2>>
  | Seq e1 e2 => Seq (extract TCUnit <<e1>>) <<e2>>
  | Pair e1 e2 => inject TCProd (Pair <<e1>> <<e2>>)
  | Fst e => Fst (extract TCProd <<e>>)
  | Snd e => Snd (extract TCProd <<e>>)
  | InjL e => inject TCSum (InjL <<e>>)
  | InjR e => inject TCSum (InjR <<e>>)
  | Case e0 e1 e2 => Case (extract TCSum <<e0>>) <<e1>> <<e2>>
  | Fold e => inject TCRec (Fold <<e>>)
  | Unfold e => Unfold (extract TCRec <<e>>)
  end
where "<< e >>" := (back_expr e).
