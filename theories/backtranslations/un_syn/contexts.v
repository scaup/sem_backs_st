From st.lam Require Import lang types typing contexts scopedness.
From st.backtranslations.un_syn Require Import universe.base expressions typed.

(* Reserved Notation "<[ Ci ]>" (at level 4, Ci at next level). *)
Definition universe_back_ctx_item (Ci : ctx_item) : ctx :=
  match Ci with
  | CTX_Lam => [CTX_AppR (inject TCArrow); CTX_Lam]
  | CTX_AppL e2 => [CTX_AppL <<e2>>; CTX_AppR (extract TCArrow)]
  | CTX_AppR e1 => [CTX_AppR (extract TCArrow <<e1>>)]
  | CTX_LetInL e2 => [CTX_LetInL <<e2>>]
  | CTX_LetInR e1 => [CTX_LetInR <<e1>>]
  | CTX_PairL e2 =>  [CTX_AppR (inject TCProd); CTX_PairL <<e2>>]
  | CTX_PairR e1 => [CTX_AppR (inject TCProd); CTX_PairR <<e1>>]
  | CTX_Fst => [CTX_Fst; CTX_AppR (extract TCProd)]
  | CTX_Snd => [CTX_Snd; CTX_AppR (extract TCProd)]
  | CTX_InjL => [CTX_AppR (inject TCSum); CTX_InjL]
  | CTX_InjR => [CTX_AppR (inject TCSum); CTX_InjR]
  | CTX_CaseL e1 e2 => [CTX_CaseL <<e1>> <<e2>>; CTX_AppR (extract TCSum)]
  | CTX_CaseM e0 e2 => [CTX_CaseM (extract TCSum <<e0>>) <<e2>>]
  | CTX_CaseR e0 e1 => [CTX_CaseR (extract TCSum <<e0>>) <<e1>>]
  | CTX_BinOpL op e2 => [CTX_AppR (inject match op with
                                         | PlusOp => TCInt
                                         | MinusOp => TCInt
                                         | LeOp => TCBool
                                         | LtOp => TCBool
                                         | EqOp => TCBool
                                         end) ; CTX_BinOpL op (extract TCInt <<e2>>); CTX_AppR (extract TCInt)]
  | CTX_BinOpR op e1 => [CTX_AppR (inject match op with
                                         | PlusOp => TCInt
                                         | MinusOp => TCInt
                                         | LeOp => TCBool
                                         | LtOp => TCBool
                                         | EqOp => TCBool
                                         end) ; CTX_BinOpR op (extract TCInt <<e1>>); CTX_AppR (extract TCInt)]
  | CTX_IfL e1 e2 => [CTX_IfL <<e1>> <<e2>>; CTX_AppR (extract TCBool)]
  | CTX_IfM e0 e2 => [CTX_IfM (extract TCBool <<e0>>) <<e2>>]
  | CTX_IfR e0 e1 => [CTX_IfR (extract TCBool <<e0>>) <<e1>>]
  | CTX_Fold => [CTX_AppR (inject TCRec); CTX_Fold]
  | CTX_Unfold => [CTX_Unfold ; CTX_AppR (extract TCRec)]
  | CTX_GhostStep => []
  end.

Lemma universe_back_ctx_item_typed (Ci : ctx_item) n m :
    |sCi> n ⊢ₙₒ Ci ☾ m ☽ →
    |C> replicate n TUniverse ⊢ₙₒ (universe_back_ctx_item Ci) ☾ replicate m TUniverse ; TUniverse ☽ : TUniverse.
Proof.
  Ltac blaa := lazymatch goal with
           | |- typed _ (universe_back_expr ?e) TUniverse => apply back_typed
           | |- typed _ (of_val (inject ?tc)) _ => apply (inject_typed tc)
           | |- typed _ (of_val (extract ?tc)) _ => apply (extract_typed tc)
           | |- _ => econstructor
           end.
  intro H. destruct H; repeat blaa; try rewrite -replicate_S; try blaa; try done.
  destruct op; repeat blaa; try blaa; try done.
  destruct op; repeat blaa; try blaa; try done.
Qed.

Fixpoint universe_back_ctx (C : ctx) : ctx :=
  match C with
  | nil => []
  | cons Ci Ctl => universe_back_ctx_item Ci ++ (universe_back_ctx Ctl)
  end.

Lemma universe_back_ctx_typed (C : ctx) n m :
    |sC> n ⊢ₙₒ C ☾ m ☽ →
    |C> replicate n TUniverse ⊢ₙₒ (universe_back_ctx C) ☾ replicate m TUniverse ; TUniverse ☽ : TUniverse.
Proof.
  intro H. induction H.
  - constructor.
  - simpl. eapply typed_ctx_app; [by apply universe_back_ctx_item_typed | auto].
Qed.
