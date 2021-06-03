From iris.program_logic Require Import language ectxi_language ectx_language lifting.
From iris Require Import program_logic.weakestpre.
From iris.proofmode Require Import tactics.
From st.lamst Require Import lang.

Section wkpre_lemmas.

  Context `{Σ : !gFunctors}.
  Context `{irisG_inst : !irisG lamst_lang Σ}.

  Lemma wp_bind' (K : list ectx_item) s E e Φ :
    WP e @ s; E {{ v, WP fill K (of_val v) @ s; E {{ Φ }} }} ⊢ WP fill K e @ s; E {{ Φ }}.
  Proof. iApply wp_bind. Qed.

  Lemma wp_pure_step_later {s : stuckness} {E : coPset} e1 e2 Φ (H : pure_step e1 e2) :
    ▷ WP e2 @ s ; E {{Φ}} ⊢ WP e1 @ s ; E {{Φ}}.
  Proof. iIntros "He2". iApply (wp_pure_step_later _ _ _ _ True 1). intros t. by apply nsteps_once. auto. auto. Qed.

End wkpre_lemmas.
