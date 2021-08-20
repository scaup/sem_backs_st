From st.STLCmuVS Require Import lang typing contexts scopedness.
From st.STLCmu Require Import types.
From st.backtranslations.sem_syn.sem_le_syn Require Import guard_assert.
From st.backtranslations.sem_syn Require Import gamma_lib.

Definition ga_ctx_nil (C : ctx) (τ : type) : ctx :=
  [CTX_AppR (ga_pair Assert TUnit)] ++ C ++ [CTX_AppR (ga_pair Guard τ)].

Definition ga_ctx_cons (C : ctx) (Γ : list type) (τ : type) : ctx :=
  let P : expr :=
      let filled_hole : expr :=
          ga_pair Guard τ (
                    wrap_funs_vars (Var (length Γ)) 0
                             ((fun τ => ga_pair Assert τ) <$> Γ)
                  )
      in
      fill_ctx C filled_hole
  in
  [CTX_LetInL (ga_pair Assert TUnit P)] ++ (LamGamma_ctx (length Γ)).

Definition ga_ctx (C : ctx) (Γ : list type) (τ : type) : ctx :=
  match (length Γ) with
  | 0 => ga_ctx_nil C τ
  | S n => ga_ctx_cons C Γ τ
  end.
