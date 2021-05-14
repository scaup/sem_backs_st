From st.lamst Require Import lang.
From st.lam Require Import lang.
From st.backtranslations.st_sem Require Import heap.

Reserved Notation "<< e >>" (at level 4, e at next level).
Fixpoint back_expr (e : lamst.lang.expr) : expr :=
  match e with
  | lamst.lang.Var x => Var x
  | lamst.lang.LetIn e1 e2 => LetIn <<e1>> <<e2>>
  | lamst.lang.Lam e => Lam <<e>>
  | lamst.lang.App e1 e2 => App <<e1>> <<e2>>
  | lamst.lang.Lit l => match l with
                       | lamst.lang.LitInt n => n
                       | lamst.lang.LitBool b => b
                       | lamst.lang.LitUnit => LitUnit
                       | LitLoc l => ()%Eₙₒ (* we only care about surface lang *)
                       end
  | lamst.lang.BinOp op e1 e2 => BinOp op <<e1>> <<e2>>
  | lamst.lang.If e0 e1 e2 => If <<e0>> <<e1>> <<e2>>
  | lamst.lang.Seq e1 e2 => Seq <<e1>> <<e2>>
  | lamst.lang.Pair e1 e2 => Pair <<e1>> <<e2>>
  | lamst.lang.Fst e => Fst <<e>>
  | lamst.lang.Snd e => Snd <<e>>
  | lamst.lang.InjL e => InjL <<e>>
  | lamst.lang.InjR e => InjR <<e>>
  | lamst.lang.Case e0 e1 e2 => Case <<e0>> <<e1>> <<e2>>
  | lamst.lang.Fold e => Fold <<e>>
  | lamst.lang.Unfold e => Unfold <<e>>
  | Return e => retrn <<e>>
  | Bind e1 e2 => bind <<e1>> <<e2>>
  | RunST e => runst <<e>>
  | Alloc e => alloc <<e>>
  | Read e => read <<e>>
  | Write e1 e2 => write <<e1>> <<e2>>
  | Compare e1 e2 => (<<e1>> = <<e2>>)%Eₙₒ
  end
where "<< e >>" := (back_expr e).
