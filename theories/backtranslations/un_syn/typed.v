From st.lam Require Import lang types typing lib.universe.base.
From st.backtranslations.un_syn Require Import expressions.

Lemma back_typed (e : expr) n (pCn : Closed_n n e) : (replicate n TUniverse) ⊢ₙₒ <<e>> : TUniverse.
Proof.
  generalize dependent n.
  induction e; intros n pCn; simpl; try by repeat (apply inject_typed || rewrite -replicate_S || apply extract_typed || apply IHe || apply IHe0 || apply IHe1 || apply IHe2 || apply IHe3 || closed_solver || econstructor).
  - econstructor. apply lookup_replicate_2. by apply Var_closed_n_lt.
  - specialize (IHe n). specialize (IHe0 (S n)).
    eapply LetIn_typed. apply IHe0. closed_solver. apply IHe. closed_solver.
  - repeat (apply inject_typed || rewrite -replicate_S || apply (extract_typed TCArrow) || apply IHe1 || apply IHe2 || closed_solver || econstructor).
  - destruct l; repeat (apply inject_typed || econstructor).
  - destruct op; repeat (apply inject_typed || apply (extract_typed) || apply IHe1 || apply IHe2 || econstructor || closed_solver).
  - repeat (apply inject_typed || apply (extract_typed TCProd) || closed_solver || apply IHe || econstructor).
  - repeat (apply inject_typed || apply (extract_typed TCProd) || closed_solver || apply IHe || econstructor).
  - specialize (IHe0 (S n)). specialize (IHe1 (S n)). repeat (apply inject_typed || apply (extract_typed TCSum) || closed_solver || apply IHe || apply IHe0 || apply IHe1 || econstructor).
  - assert (TUniverse = TUniverse.[TRec TUniverse/]) as eq. by asimpl. rewrite eq. econstructor. econstructor.
    apply extract_typed. rewrite -eq. apply IHe. closed_solver.
Qed.
