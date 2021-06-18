From st.lam Require Import lang typing types nr_types contexts scopedness.
From st.backtranslations.un_syn Require Import universe.base expressions contexts typed.
From st.backtranslations.sem_syn Require Import nr_embed_project gamma_lib.
From st.prelude Require Import forall_three.

Definition uni_back_ctx_cons (C : ctx) (Γ : list nr_type) (τ : nr_type) : ctx :=
  let P : expr :=
      let filled_hole : expr :=
          ep_pair τ Embed (
                    wrap_funs_vars (Var (length Γ)) 0
                             ((fun τ => ep_pair τ Project) <$> Γ)
                  )
      in
      fill_ctx (back_ctx C) filled_hole
  in
  [CTX_LetInL (ep_pair NRTUnit Project P)] ++ (LamGamma_ctx (length Γ)).

Definition uni_back_ctx_nil (C : ctx) (τ : nr_type) : ctx :=
  [CTX_AppR (ep_pair NRTUnit Project)] ++ back_ctx C ++ [CTX_AppR (ep_pair τ Embed)].

Opaque ep_pair.

Lemma uni_back_ctx_cons_typed (C : ctx) (Γ : list nr_type) (τ : nr_type)
  (H : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽) :
  |C> [] ⊢ₙₒ (uni_back_ctx_cons C Γ τ) ☾ map nr_type_type Γ ; τ ☽ : TUnit.
Proof.
  eapply typed_ctx_app; [|rewrite -(map_length nr_type_type Γ); apply LamGamma_ctx_typed].
  econstructor. 2: constructor. simpl.
  constructor. apply App_typed with (τ1 := TUniverse). apply ep_pair_typed.
  eapply typed_ctx_typed with (Γ := (map (fun _ => TUniverse) Γ) ++ [GammaType (map nr_type_type Γ) τ]) (τ := TUniverse).
  apply App_typed with (τ1 := τ). apply ep_pair_typed.
  rewrite -(map_length (fun _ => TUniverse) Γ). apply wrap_funs_vars_typed.
  apply Forall3_fmap_r, Forall3_fmap_l, Forall3_fmap_m, Forall3_same, Forall_true.
  simpl. intros. apply ep_pair_typed.
  change [GammaType (map nr_type_type Γ) τ] with ([] ++ [GammaType (map nr_type_type Γ) τ]) at 2.
  apply typed_ctx_append. change [] with (replicate 0 TUniverse).
  replace (map (fun _ => TUniverse) Γ) with (replicate (length Γ) TUniverse).
  by apply back_ctx_typed. rewrite -(const_fmap (fun _ => TUniverse)); auto.
Qed.

Lemma uni_back_ctx_nil_typed (C : ctx) (τ : nr_type)
  (H : |sC> 0 ⊢ₙₒ C ☾ 0 ☽) :
  |C> [] ⊢ₙₒ (uni_back_ctx_nil C τ) ☾ [] ; τ ☽ : TUnit.
Proof.
  rewrite /uni_back_ctx_nil. eapply typed_ctx_app. econstructor. constructor. instantiate (1 := TUniverse).
  apply ep_pair_typed. constructor.
  eapply typed_ctx_app. change [] with (replicate 0 TUniverse).
  apply back_ctx_typed. eauto. econstructor. constructor. instantiate (1 := τ).
  apply ep_pair_typed. constructor.
Qed.

