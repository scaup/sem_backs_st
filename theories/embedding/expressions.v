From st.STLCmuVS Require Import lang.
From st.STLCmuST Require Import lang.

Reserved Notation "[[ e ]]" (at level 4, e at next level).
Fixpoint embd_expr (e : STLCmuVS.lang.expr) : expr :=
  match e with
  | STLCmuVS.lang.Var x => Var x
  | STLCmuVS.lang.LetIn e1 e2 => LetIn [[e1]] [[e2]]
  | STLCmuVS.lang.Lam e => Lam [[e]]
  | STLCmuVS.lang.App e1 e2 => App [[e1]] [[e2]]
  | STLCmuVS.lang.Lit l => match l with
                       | STLCmuVS.lang.LitInt n => n
                       | STLCmuVS.lang.LitBool b => b
                       | STLCmuVS.lang.LitUnit => LitUnit
                       end
  | STLCmuVS.lang.BinOp op e1 e2 => BinOp op [[e1]] [[e2]]
  | STLCmuVS.lang.If e0 e1 e2 => If [[e0]] [[e1]] [[e2]]
  | STLCmuVS.lang.Seq e1 e2 => Seq [[e1]] [[e2]]
  | STLCmuVS.lang.Pair e1 e2 => Pair [[e1]] [[e2]]
  | STLCmuVS.lang.Fst e => Fst [[e]]
  | STLCmuVS.lang.Snd e => Snd [[e]]
  | STLCmuVS.lang.InjL e => InjL [[e]]
  | STLCmuVS.lang.InjR e => InjR [[e]]
  | STLCmuVS.lang.Case e0 e1 e2 => Case [[e0]] [[e1]] [[e2]]
  | STLCmuVS.lang.Fold e => Fold [[e]]
  | STLCmuVS.lang.Unfold e => Unfold [[e]]
  | STLCmuVS.lang.VirtStep e => Lam [[e]]%Eₛₜ (* just a dummy value; we only care about embedding syntactically well-typed expressions *)
  end
where "[[ e ]]" := (embd_expr e).
