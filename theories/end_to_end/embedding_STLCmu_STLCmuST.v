From st.STLCmu Require Import lang.
From st.STLCmuST Require Import lang.
From st.prelude Require Import lang_base.

Reserved Notation "[[ e ]]" (at level 4, e at next level).
Fixpoint embd_expr (e : STLCmu.lang.expr) : STLCmuST.lang.expr :=
  match e with
  | STLCmu.lang.Var x => Var x
  | STLCmu.lang.LetIn e1 e2 => LetIn [[e1]] [[e2]]
  | STLCmu.lang.Lam e => Lam [[e]]
  | STLCmu.lang.App e1 e2 => App [[e1]] [[e2]]
  | STLCmu.lang.Lit l => match l with
                       | LitInt n => n
                       | LitBool b => b
                       | LitUnit => ()%Eₛₜ
                       end
  | STLCmu.lang.BinOp op e1 e2 => BinOp op [[e1]] [[e2]]
  | STLCmu.lang.If e0 e1 e2 => If [[e0]] [[e1]] [[e2]]
  | STLCmu.lang.Seq e1 e2 => Seq [[e1]] [[e2]]
  | STLCmu.lang.Pair e1 e2 => Pair [[e1]] [[e2]]
  | STLCmu.lang.Fst e => Fst [[e]]
  | STLCmu.lang.Snd e => Snd [[e]]
  | STLCmu.lang.InjL e => InjL [[e]]
  | STLCmu.lang.InjR e => InjR [[e]]
  | STLCmu.lang.Case e0 e1 e2 => Case [[e0]] [[e1]] [[e2]]
  | STLCmu.lang.Fold e => Fold [[e]]
  | STLCmu.lang.Unfold e => Unfold [[e]]
  end
where "[[ e ]]" := (embd_expr e).

From st.STLCmu Require Import contexts.
From st.STLCmuST Require Import contexts.

Definition embd_ctx_item (Ci : STLCmu.contexts.ctx_item) : STLCmuST.contexts.ctx_item :=
  match Ci with
  | STLCmu.contexts.CTX_Lam => CTX_Lam
  | STLCmu.contexts.CTX_AppL e2 => CTX_AppL [[e2]]
  | STLCmu.contexts.CTX_AppR e1 => CTX_AppR [[e1]]
  | STLCmu.contexts.CTX_LetInL e2 => CTX_LetInL [[e2]]
  | STLCmu.contexts.CTX_LetInR e1 => CTX_LetInR [[e1]]
  | STLCmu.contexts.CTX_PairL e2 => CTX_PairL [[e2]]
  | STLCmu.contexts.CTX_PairR e1 => CTX_PairR [[e1]]
  | STLCmu.contexts.CTX_Fst => CTX_Fst
  | STLCmu.contexts.CTX_Snd => CTX_Snd
  | STLCmu.contexts.CTX_InjL => CTX_InjL
  | STLCmu.contexts.CTX_InjR => CTX_InjR
  | STLCmu.contexts.CTX_CaseL e1 e2 => CTX_CaseL [[e1]] [[e2]]
  | STLCmu.contexts.CTX_CaseM e0 e2 => CTX_CaseM [[e0]] [[e2]]
  | STLCmu.contexts.CTX_CaseR e0 e1 => CTX_CaseR [[e0]] [[e1]]
  | STLCmu.contexts.CTX_BinOpL op e2 => CTX_BinOpL op [[e2]]
  | STLCmu.contexts.CTX_BinOpR op e1 => CTX_BinOpR op [[e1]]
  | STLCmu.contexts.CTX_IfL e1 e2 => CTX_IfL [[e1]] [[e2]]
  | STLCmu.contexts.CTX_IfM e0 e2 => CTX_IfM [[e0]] [[e2]]
  | STLCmu.contexts.CTX_IfR e0 e1 => CTX_IfR [[e0]] [[e1]]
  | STLCmu.contexts.CTX_Fold => CTX_Fold
  | STLCmu.contexts.CTX_Unfold => CTX_Unfold
  end.

Definition embd_ctx (C : STLCmu.contexts.ctx) : STLCmuST.contexts.ctx :=
  fmap embd_ctx_item C.
