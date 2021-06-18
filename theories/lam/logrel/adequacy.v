(* From iris Require Import program_logic.weakestpre. *)
(* From iris.base_logic.lib Require Import invariants gen_heap wsat ghost_map. *)
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
(* From iris.base_logic.lib Require Import invariants gen_heap. *)
From st.lam Require Import lang types logrel.definitions.
(* From st.lamst Require Import wkpre lang types. *)
(* From st.backtranslations.st_sem.correctness.st_le_sem.logrel Require Import definition lift. *)
From st Require Import resources.

Definition Σ : gFunctors :=
  #[invΣ; ghost_mapΣ nat (val * val)].

Instance lam_irisG_inst (H : invG Σ) : irisG lam_lang Σ :=
  { iris_invG := H;
    state_interp σ _ κs _ := True%I;
    fork_post v := True%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _;
  }.

Instance semΣ_inst (H : invG Σ) : semΣ Σ :=
  { irisG_inst := _ ;
    ghost_mapG_inst := _ ;
  }.

Lemma exprel_adequate (e : expr) (e' : lam.lang.expr)
      (Hee' : ∀ {Σ : gFunctors} {semΣ_inst : semΣ Σ}, ⊢ exprel_typed MaybeStuck TUnit e e') :
  lam_halts e → lam_halts e'.
Proof.
  intros He. destruct He as (v & He).
  cut (adequate MaybeStuck e tt (fun _ _ => lam_halts e')).
  { intro Ha. apply (adequate_result _ _ _ _ Ha [] tt v).
    change ([?e], tt) with ((fun x => ([x], tt)) e).
    eapply (rtc_congruence (fun x => ([x], tt))); eauto.
    intros e1 e2 Hstep. rewrite /lam_step in Hstep.
    rewrite /erased_step /=. exists []. apply (step_atomic e1 tt e2 tt [] [] []); by simpl. }
  apply (wp_adequacy Σ lam_lang MaybeStuck e tt (fun _ => lam_halts e')).
  { intros invG_inst' κs.
    iExists (fun _ _ => True%I). iExists (fun _ => True%I).
    iModIntro. iSplit; auto.
    iDestruct (Hee' Σ _) as "Hee'".
    iApply (wp_wand with "Hee'").
    iIntros (w) "Hdes". iDestruct "Hdes" as (w') "[%He' _]".
    iPureIntro. by eexists.
  }
Qed.
