From st.STLCmuST Require Import lang.
From st.lam Require Import lang.
From st.backtranslations.st_sem Require Import heap_emul.base.

Reserved Notation "<< e >>" (at level 4, e at next level).
Fixpoint back_expr (e : STLCmuST.lang.expr) : expr :=
  match e with
  | STLCmuST.lang.Var x => Var x
  | STLCmuST.lang.LetIn e1 e2 => LetIn <<e1>> <<e2>>
  | STLCmuST.lang.Lam e => Lam <<e>>
  | STLCmuST.lang.App e1 e2 => App <<e1>> <<e2>>
  | STLCmuST.lang.Lit l => match l with
                       | STLCmuST.lang.LitInt n => n
                       | STLCmuST.lang.LitBool b => b
                       | STLCmuST.lang.LitUnit => LitUnit
                       | LitLoc l => ()%Eₙₒ (* we only care about surface lang *)
                       end
  | STLCmuST.lang.BinOp op e1 e2 => BinOp op <<e1>> <<e2>>
  | STLCmuST.lang.If e0 e1 e2 => If <<e0>> <<e1>> <<e2>>
  | STLCmuST.lang.Seq e1 e2 => Seq <<e1>> <<e2>>
  | STLCmuST.lang.Pair e1 e2 => Pair <<e1>> <<e2>>
  | STLCmuST.lang.Fst e => Fst <<e>>
  | STLCmuST.lang.Snd e => Snd <<e>>
  | STLCmuST.lang.InjL e => InjL <<e>>
  | STLCmuST.lang.InjR e => InjR <<e>>
  | STLCmuST.lang.Case e0 e1 e2 => Case <<e0>> <<e1>> <<e2>>
  | STLCmuST.lang.Fold e => Fold <<e>>
  | STLCmuST.lang.Unfold e => Unfold <<e>>
  | Return e => retrn <<e>>
  | Bind e1 e2 => bind <<e1>> <<e2>>
  | RunST e => runst <<e>>
  | Alloc e => alloc <<e>>
  | Read e => read <<e>>
  | Write e1 e2 => write <<e1>> <<e2>>
  | Compare e1 e2 => (<<e1>> = <<e2>>)%Eₙₒ
  end
where "<< e >>" := (back_expr e).
