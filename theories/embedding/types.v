From st Require Import lam.types lamst.types.
From st.prelude Require Export generic autosubst.

Fixpoint embed (τ : lam.types.type) : lamst.types.type :=
  match τ with
  | lam.types.TUnit => TUnit
  | lam.types.TBool => TBool
  | lam.types.TInt => TInt
  | lam.types.TProd τ1 τ2 => TProd (embed τ1) (embed τ2)
  | lam.types.TSum τ1 τ2 => TSum (embed τ1) (embed τ2)
  | lam.types.TArrow τ1 τ2 => TArrow (embed τ1) (embed τ2)
  | lam.types.TRec τb => TRec (embed τb)
  | lam.types.TVar X => TVar X
  end.

Notation "[| τ |]" := (embed τ) (at level 4, τ at next level).

Lemma etype_ren_gen τ :
  forall k l, [| τ.[upn l (ren (+k))] |] = [|τ|].[upn l (ren (+k))].
Proof.
  induction τ; intros k l; try by asimpl.
  - asimpl. by rewrite IHτ1 IHτ2.
  - asimpl. by rewrite IHτ1 IHτ2.
  - asimpl. by rewrite IHτ1 IHτ2.
  - simpl. specialize (IHτ k (S l)). by rewrite IHτ.
  - asimpl. do 2 rewrite (iter_up l X (ren (+k))).
    destruct (lt_dec X l); by asimpl.
Qed.

Lemma embed_TRec_comm_gen (τb : lam.types.type) : forall (τ : lam.types.type) k,
  [| τb.[upn k (τ .: ids)] |] = [|τb|].[upn k ([|τ|] .: ids)].
Proof.
  induction τb; intros τ' k; try by asimpl.
  - asimpl. by rewrite IHτb1 IHτb2.
  - asimpl. by rewrite IHτb1 IHτb2.
  - asimpl. by rewrite IHτb1 IHτb2.
  - simpl. specialize (IHτb τ' (S k)). by rewrite IHτb.
  - asimpl.
    rewrite (iter_up k X (τ' .: ids)) (iter_up k X ([|τ'|] .: ids)).
    destruct (lt_dec X k).
      + by asimpl.
      + destruct (decide (X - k = 0)); asimpl. rewrite e. asimpl.
        cut ([| τ'.[upn 0 (ren (+k))] |] = ([| τ' |]).[upn 0 (ren (+k))]).
        by asimpl. by rewrite etype_ren_gen.
        destruct (X - k). exfalso; lia. by asimpl.
Qed.

Lemma embed_TRec_comm (τb : lam.types.type) :
  [| τb.[lam.types.TRec τb/]|] = [|τb|].[TRec [|τb|]/].
Proof.
  cut ([| (τb.[upn 0 ((lam.types.TRec τb) .: ids)])|] = [|τb|].[upn 0 ([|(lam.types.TRec τb)|] .: ids)]).
  by asimpl. apply embed_TRec_comm_gen.
Qed.
