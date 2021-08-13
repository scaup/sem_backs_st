From st.lam Require Import lang.

Fixpoint ectx_expr (e : expr) : list ectx_item :=
  match e with
  | Var x => []
  | LetIn e1 e2 => match to_val e1 with
                 | Some v1 => []
                 | None =>  ectx_expr e1 ++ [LetInCtx e2]
                 end
  | Lam e => []
  (* | Fix e => match to_val e with *)
            (* | Some v => [] *)
            (* | None => ectx_expr e ++ [FixCtx] *)
            (* end *)
  | App e1 e2 => match to_val e1 with
                | Some v1 => match to_val e2 with
                            | Some v2 => []
                            | None => ectx_expr e2 ++ [AppRCtx v1]
                         end
                | None => ectx_expr e1 ++ [AppLCtx e2]
                end
  | Lit l => []
  | BinOp op e1 e2 => match to_val e1 with
                     | Some v1 => match to_val e2 with
                                 | Some v2 => []
                                 | None => ectx_expr e2 ++ [BinOpRCtx op v1]
                                 end
                     | None => ectx_expr e1 ++ [BinOpLCtx op e2]
                     end
  | If e0 e1 e2 => match to_val e0 with
                  | Some v0 => []
                  | None => ectx_expr e0 ++ [IfCtx e1 e2]
                  end
  | Seq e1 e2 => match to_val e1 with
                | Some v1 => []
                | None => ectx_expr e1 ++ [SeqCtx e2]
                end
  | Pair e1 e2 => match to_val e1 with
                 | Some v1 => match to_val e2 with
                             | Some v2 => []
                             | None => ectx_expr e2 ++ [PairRCtx v1]
                             end
                 | None => ectx_expr e1 ++ [PairLCtx e2]
                 end
  | Fst e => match to_val e with
            | Some v => []
            | None => ectx_expr e ++ [FstCtx]
            end
  | Snd e => match to_val e with
            | Some v => []
            | None => ectx_expr e ++ [SndCtx]
            end
  | InjL e => match to_val e with
             | Some v => []
             | None => ectx_expr e ++ [InjLCtx]
             end
  | InjR e => match to_val e with
             | Some v => []
             | None => ectx_expr e ++ [InjRCtx]
             end
  | Case e0 e1 e2 => match to_val e0 with
                    | Some v0 => []
                    | None => ectx_expr e0 ++ [CaseCtx e1 e2]
                    end
  | Fold e => match to_val e with
                | Some v => []
                | None => ectx_expr e ++ [FoldCtx]
                end
  | Unfold e => match to_val e with
                | Some v => []
                | None => ectx_expr e ++ [UnfoldCtx]
                end
  (* | TLam e => [] *)
  (* | TApp e => match to_val e with *)
             (* | Some v => [] *)
             (* | None => ectx_expr e ++ [TAppCtx] *)
             (* end *)
  | GhostStep e => match to_val e with
                | Some v => []
                | None => ectx_expr e ++ [GhostStepCtx]
                end
  end.


Fixpoint head_expr (e : expr) : expr :=
  match e with
  | Var x => Var x
  | LetIn e1 e2 => match to_val e1 with
                 | Some v1 => LetIn v1 e2
                 | None => head_expr e1
                 end
  | Lam e => LamV e
  (* | Fix e => match to_val e with *)
            (* | Some v => Fix v *)
            (* | None => head_expr e *)
            (* end *)
  | App e1 e2 => match to_val e1 with
                | Some v1 => match to_val e2 with
                            | Some v2 => App v1 v2
                            | None => head_expr e2
                         end
                | None => head_expr e1
                end
  | Lit l => LitV l
  | BinOp op e1 e2 => match to_val e1 with
                     | Some v1 => match to_val e2 with
                                 | Some v2 => BinOp op v1 v2
                                 | None => head_expr e2
                                 end
                     | None => head_expr e1
                     end
  | If e0 e1 e2 => match to_val e0 with
                  | Some v0 => If v0 e1 e2
                  | None => head_expr e0
                  end
  | Seq e1 e2 => match to_val e1 with
                | Some v1 => Seq v1 e2
                | None =>  head_expr e1
                end
  | Pair e1 e2 => match to_val e1 with
                 | Some v1 => match to_val e2 with
                             | Some v2 => Pair v1 v2
                             | None => head_expr e2
                             end
                 | None => head_expr e1
                 end
  | Fst e => match to_val e with
            | Some v => Fst v
            | None => head_expr e
            end
  | Snd e => match to_val e with
            | Some v => Snd v
            | None => head_expr e
            end
  | InjL e => match to_val e with
             | Some v => InjLV v
             | None => head_expr e
             end
  | InjR e => match to_val e with
             | Some v => InjRV v
             | None => head_expr e
             end
  | Case e0 e1 e2 => match to_val e0 with
                    | Some v0 => Case v0 e1 e2
                    | None => head_expr e0
                    end
  | Fold e => match to_val e with
             | Some v => FoldV v
             | None => head_expr e
             end
  | Unfold e => match to_val e with
                | Some v => Unfold v
                | None => head_expr e
                end
  (* | TLam e => TLamV e *)
  (* | TApp e => match to_val e with *)
             (* | Some v => TApp v *)
             (* | None => head_expr e *)
             (* end *)
  | GhostStep e => match to_val e with
                  | Some v => GhostStep v
                  | None => head_expr e
                  end
  end.

(* Lemma prim_step_pure e σ κ e' : prim_step e [] e' [] → pure_step e e'. *)
(* Proof. *)
(*   intro Hp. split. *)
(*   + intro σ. destruct σ. exists e', tt, []. by simpl. *)
(*   + intros. destruct σ1, σ2. simpl in H. *)
(*     assert (efs = []) as ->; first by inversion H. assert (κ = []) as ->; first by inversion H. *)
(*     erewrite (prim_step_det e e' e2'); eauto. *)
(* Qed. *)


Lemma split_expr (e : expr) : e = fill (ectx_expr e) (head_expr e).
Proof.
  induction e as [x | e1 IH1 e2 IH2 | e1 IH1 | e1 IH1 e2 IH2 | e1 | binop e1 IH1 e2 IH2 | e1 IH1 e2 IH2 e3 IH3 | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e1 IH1 | e1 IH1 | e1 IH1 | e1 IH1 | e1 IH1 e2 IH2 | e1 IH1 | e1 IH1 | e1 IH1 ];
    try done; repeat ((destruct (to_val e1) eqn:eq1 || destruct (to_val e2) eqn:eq2 || rewrite fill_app || rewrite (of_to_val _ _ eq1) || rewrite (of_to_val _ _ eq2) || rewrite eq1 || rewrite eq2 || rewrite -IH1 || rewrite -IH2 || simpl)); auto.
Qed.

Ltac simplify_custom := (simplify_option_eq; asimpl; (repeat (rewrite to_of_val /=; asimpl)); simplify_option_eq).

Ltac auto_head_step :=
  lazymatch goal with
  | |- head_step _ _ _ _ _ _ => by (simplify_custom; econstructor; simplify_custom)
  | |- ectx_language.head_step _ _ _ _ _ _ => by (simplify_custom; econstructor; simplify_custom)
  | |- _ => fail "Goal not a head_step"
  end.

Ltac ectx_lam_step :=
  lazymatch goal with
  | |- lam_step ?e _ => eapply (Ectx_step (ectx_expr e) (head_expr e) _ (split_expr e)); first eauto
  | |- _ => fail "Goal not a lam_step"
  end.

Ltac auto_lam_step :=
  lazymatch goal with
  | |- lam_step ?e _ => by (ectx_lam_step; auto_head_step)
  | |- _ => fail "Goal not a lam_step"
  end.

Ltac auto_rtc_lam_step :=
  lazymatch goal with
  | |- rtc lam_step ?e ?e => by apply rtc_refl
  | |- rtc lam_step _ _ => (eapply rtc_l; first (auto_lam_step); simplify_custom)
  | |- _ => fail "Goal not a rtc lam_step"
  end.

(* Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances. *)
(* Hint Extern 10 (IntoVal _ _) => *)
(*   rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances. *)

