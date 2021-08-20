From st.STLCmuVS Require Import lang typing contexts scopedness.
From st.STLCmu Require Import types.
From st.backtranslations.un_syn Require Import universe.base expressions contexts typed.
From st.backtranslations.sem_syn Require Import embed_project gamma_lib.
From st.prelude Require Import forall_three.

Definition back_ctx_nil (C : ctx) (τ : type) : ctx :=
  [CTX_AppR (ep_pair Project TUnit)] ++ universe_back_ctx C ++ [CTX_AppR (ep_pair Embed τ)].

Definition back_ctx_cons (C : ctx) (Γ : list type) (τ : type) : ctx :=
  let P : expr :=
      let filled_hole : expr :=
          ep_pair Embed τ (
                    wrap_funs_vars (Var (length Γ)) 0
                             ((fun τ => ep_pair Project τ) <$> Γ)
                  )
      in
      fill_ctx (universe_back_ctx C) filled_hole
  in
  [CTX_LetInL (ep_pair Project TUnit P)] ++ (LamGamma_ctx (length Γ)).

Definition back_ctx (C : ctx) (Γ : list type) (τ : type) : ctx :=
  match (length Γ) with
  | 0 => back_ctx_nil C τ
  | S n => back_ctx_cons C Γ τ
  end.

Lemma back_ctx_nil_typed (C : ctx) (τ : type) (pτ : Closed τ)
  (H : |sC> 0 ⊢ₙₒ C ☾ 0 ☽) :
  |C> [] ⊢ₙₒ (back_ctx_nil C τ) ☾ [] ; τ ☽ : TUnit.
Proof.
  rewrite /back_ctx_nil. eapply typed_ctx_app. econstructor. constructor. instantiate (1 := TUniverse).
  apply ep_pair_typed. intro σ; by asimpl. constructor.
  eapply typed_ctx_app. change [] with (replicate 0 TUniverse).
  apply universe_back_ctx_typed. eauto. econstructor. constructor. instantiate (1 := τ).
  apply ep_pair_typed. auto. constructor.
Qed.

Lemma back_ctx_cons_typed (C : ctx) (Γ : list type) (pΓ : Forall Closed Γ) (τ : type) (pτ : Closed τ)
  (H : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽) :
  |C> [] ⊢ₙₒ (back_ctx_cons C Γ τ) ☾ Γ ; τ ☽ : TUnit.
Proof.
  Opaque ep_pair.
  eapply typed_ctx_app; [| apply LamGamma_ctx_typed].
  econstructor. 2: constructor. simpl.
  constructor. apply App_typed with (τ1 := TUniverse). apply typed_nil, ep_pair_typed. intros σ; by asimpl.
  eapply typed_ctx_typed with (Γ := (map (fun _ => TUniverse) Γ) ++ [GammaType Γ τ]) (τ := TUniverse).
  apply App_typed with (τ1 := τ). apply typed_nil, ep_pair_typed; auto.
  rewrite -(map_length (fun _ => TUniverse) Γ). apply wrap_funs_vars_typed.
  apply Forall3_fmap_l, Forall3_fmap_m, Forall3_same. eapply Forall_impl; eauto.
  simpl. intros. apply typed_nil, ep_pair_typed. auto.
  change [GammaType Γ τ] with ([] ++ [GammaType Γ τ]) at 2.
  apply typed_ctx_append. change [] with (replicate 0 TUniverse).
  replace (map (fun _ => TUniverse) Γ) with (replicate (length Γ) TUniverse).
  by apply universe_back_ctx_typed. rewrite -(const_fmap (fun _ => TUniverse)); auto.
Qed.

Lemma back_ctx_typed (C : ctx) (Γ : list type) (pΓ : Forall Closed Γ) (τ : type) (pτ : Closed τ)
  (H : |sC> 0 ⊢ₙₒ C ☾ length Γ ☽) :
  |C> [] ⊢ₙₒ (back_ctx C Γ τ) ☾ Γ ; τ ☽ : TUnit.
Proof.
  destruct (length Γ) eqn:eq.
  - rewrite (nil_length_inv _ eq) /=. by apply back_ctx_nil_typed.
  - rewrite /back_ctx eq. apply back_ctx_cons_typed; auto. by rewrite eq.
Qed.
