From st.STLCmuST Require Import lang contexts.
From st.lam Require Import lang contexts.
From st.backtranslations.st_sem Require Import heap_emul.base expressions.

Definition back_ctx_item (Ci : STLCmuST.contexts.ctx_item) : ctx :=
  match Ci with
  | STLCmuST.contexts.CTX_Lam => [CTX_Lam]
  | STLCmuST.contexts.CTX_AppL e2 => [CTX_AppL <<e2>>]
  | STLCmuST.contexts.CTX_AppR e1 => [CTX_AppR <<e1>>]
  | STLCmuST.contexts.CTX_LetInL e2 => [CTX_LetInL <<e2>>]
  | STLCmuST.contexts.CTX_LetInR e1 => [CTX_LetInR <<e1>>]
  | STLCmuST.contexts.CTX_PairL e2 => [CTX_PairL <<e2>>]
  | STLCmuST.contexts.CTX_PairR e1 => [CTX_PairR <<e1>>]
  | STLCmuST.contexts.CTX_Fst => [CTX_Fst]
  | STLCmuST.contexts.CTX_Snd => [CTX_Snd]
  | STLCmuST.contexts.CTX_InjL => [CTX_InjL]
  | STLCmuST.contexts.CTX_InjR => [CTX_InjR]
  | STLCmuST.contexts.CTX_CaseL e1 e2 => [CTX_CaseL <<e1>> <<e2>>]
  | STLCmuST.contexts.CTX_CaseM e0 e2 => [CTX_CaseM <<e0>> <<e2>>]
  | STLCmuST.contexts.CTX_CaseR e0 e1 => [CTX_CaseR <<e0>> <<e1>>]
  | STLCmuST.contexts.CTX_BinOpL op e2 => [CTX_BinOpL op <<e2>>]
  | STLCmuST.contexts.CTX_BinOpR op e1 => [CTX_BinOpR op <<e1>>]
  | STLCmuST.contexts.CTX_IfL e1 e2 => [CTX_IfL <<e1>> <<e2>>]
  | STLCmuST.contexts.CTX_IfM e0 e2 => [CTX_IfM <<e0>> <<e2>>]
  | STLCmuST.contexts.CTX_IfR e0 e1 => [CTX_IfR <<e0>> <<e1>>]
  | STLCmuST.contexts.CTX_Fold => [CTX_Fold]
  | STLCmuST.contexts.CTX_Unfold => [CTX_Unfold]
  | CTX_Alloc => [CTX_AppR alloc]
  | CTX_Read => [CTX_AppR read]
  | CTX_WriteL e2 => [CTX_AppL <<e2>>; CTX_AppR write]
  | CTX_WriteR e1 => [CTX_AppR (write <<e1>>)]
  | CTX_CompL e2 => [CTX_BinOpL EqOp <<e2>>]
  | CTX_CompR e1 => [CTX_BinOpR EqOp <<e1>>]
  | CTX_Return => [CTX_AppR retrn]
  | CTX_BindL e2 => [CTX_AppL <<e2>>; CTX_AppR bind]
  | CTX_BindR e1 => [CTX_AppR (bind <<e1>>)]
  | CTX_RunST => [CTX_AppR runst]
  end.

Fixpoint back_ctx (C : STLCmuST.contexts.ctx) : ctx :=
  match C with
  | nil => []
  | cons Ci Ctl => back_ctx_item Ci ++ (back_ctx Ctl)
  end.
