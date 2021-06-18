From st.lam Require Import lang types typing scopedness.
From st.backtranslations.un_syn Require Import expressions universe.base.

Lemma back_typed (e : expr) n (pCn :  expr_scoped n e) : (replicate n TUniverse) ⊢ₙₒ <<e>> : TUniverse.
Proof.
  generalize dependent n.
  induction e; intros n pCn; inversion pCn; simplify_eq; simpl; try by repeat (apply inject_typed || rewrite -replicate_S || apply extract_typed || apply IHe || apply IHe0 || apply IHe1 || apply IHe2 || apply IHe3 || closed_solver || econstructor).
  - econstructor. apply lookup_replicate_2. by inversion pCn.
  - specialize (IHe n). specialize (IHe0 (S n)).
    eapply LetIn_typed. apply IHe0. by inversion pCn. apply IHe. auto.
  - by repeat (apply inject_typed || rewrite -replicate_S || apply (extract_typed TCArrow) || apply IHe1 || apply IHe2 || econstructor).
  - destruct l; repeat (apply inject_typed || econstructor).
  - by destruct op; repeat (apply inject_typed || apply (extract_typed) || apply IHe1 || apply IHe2 || econstructor || closed_solver).
  - by repeat (apply inject_typed || apply (extract_typed TCProd) || apply IHe || econstructor).
  - by repeat (apply inject_typed || apply (extract_typed TCProd) || apply IHe || econstructor).
  - specialize (IHe0 (S n)). specialize (IHe1 (S n)). by repeat (apply inject_typed || apply (extract_typed TCSum) || apply IHe || apply IHe0 || apply IHe1 || econstructor).
  - assert (TUniverse = TUniverse.[TRec TUniverse/]) as eq. by asimpl. rewrite eq. econstructor. econstructor.
    apply extract_typed. rewrite -eq. apply IHe. done.
Qed.
