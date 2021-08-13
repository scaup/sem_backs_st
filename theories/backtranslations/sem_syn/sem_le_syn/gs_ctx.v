From st.lam Require Import lang typing types contexts scopedness.
From st.backtranslations.sem_syn Require Import gamma_lib.

Definition gs_ctx_nil (C : ctx) : ctx :=
  [CTX_GhostStep] ++ C ++ [CTX_GhostStep].

Definition gs_ctx_cons (C : ctx) (n : nat) : ctx :=
  let P : expr :=
      let filled_hole : expr :=
          GhostStep (
              wrap_funs_vars (Var n) 0
                             (replicate n (LamV (GhostStep (Var 0))))
            )
      in
      fill_ctx C filled_hole
  in
  [CTX_LetInL (GhostStep P)] ++ (LamGamma_ctx n).

Definition gs_ctx (C : ctx) n : ctx :=
  match n with
  | 0 => gs_ctx_nil C
  | S x => gs_ctx_cons C n
  end.
