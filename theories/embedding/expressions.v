From st.lam Require Import lang.
From st.lamst Require Import lang.

Reserved Notation "[[ e ]]" (at level 4, e at next level).
Fixpoint embd_expr (e : lam.lang.expr) : expr :=
  match e with
  | lam.lang.Var x => Var x
  | lam.lang.LetIn e1 e2 => LetIn [[e1]] [[e2]]
  | lam.lang.Lam e => Lam [[e]]
  | lam.lang.App e1 e2 => App [[e1]] [[e2]]
  | lam.lang.Lit l => match l with
                       | lam.lang.LitInt n => n
                       | lam.lang.LitBool b => b
                       | lam.lang.LitUnit => LitUnit
                       end
  | lam.lang.BinOp op e1 e2 => BinOp op [[e1]] [[e2]]
  | lam.lang.If e0 e1 e2 => If [[e0]] [[e1]] [[e2]]
  | lam.lang.Seq e1 e2 => Seq [[e1]] [[e2]]
  | lam.lang.Pair e1 e2 => Pair [[e1]] [[e2]]
  | lam.lang.Fst e => Fst [[e]]
  | lam.lang.Snd e => Snd [[e]]
  | lam.lang.InjL e => InjL [[e]]
  | lam.lang.InjR e => InjR [[e]]
  | lam.lang.Case e0 e1 e2 => Case [[e0]] [[e1]] [[e2]]
  | lam.lang.Fold e => Fold [[e]]
  | lam.lang.Unfold e => Unfold [[e]]
  end
where "[[ e ]]" := (embd_expr e).
