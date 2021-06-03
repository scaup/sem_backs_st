From iris.base_logic.lib Require Import invariants gen_heap wsat ghost_map.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.
From st.lamst Require Import lang types.
From st.lam Require Import wkpre lang.
From st.backtranslations.st_sem.correctness.sem_le_st.logrel Require Import definition lift.

Definition Σ : gFunctors :=
  #[invΣ;
    gen_heapΣ loc lamst.lang.val;
    ghost_mapΣ nat lam.lang.val;
    ghost_mapΣ nat loc
    ].

Instance lam_irisG_inst (H : invG Σ) : irisG lam_lang Σ :=
  { iris_invG := H;
    state_interp σ _ κs _ := True%I;
    fork_post v := True%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _;
  }.

Lemma exprel_adequate (e : expr) (e' : lamst.lang.expr)
      (Hee' : ∀ {Σ : gFunctors}
                {irisG_inst : irisG lam_lang Σ}
                {genHeapG_inst : gen_heapG loc lamst.lang.val Σ}
                {val_ghost_mapG_inst : ghost_mapG Σ nat val}
                {loc_ghost_mapG_inst : ghost_mapG Σ nat loc},
          ⊢ exprel_typed [] TUnit e e') :
  lam_halts e → lamst_halts e'.
Proof.
  intros He. destruct He as (v & He).
  cut (adequate MaybeStuck e tt (fun _ _ => lamst_halts e')).
  { intro Ha. apply (adequate_result _ _ _ _ Ha [] tt v).
    change ([?e], ?σ) with ((fun x => ([x], tt)) e).
    eapply (rtc_congruence (fun x => ([x], tt))); eauto.
    intros e1 e2 Hstep. rewrite /lam_step in Hstep.
    rewrite /erased_step /=. exists []. apply (step_atomic e1 tt e2 tt [] [] []); by simpl. }
  apply (wp_adequacy Σ lam_lang MaybeStuck e tt (fun _ => lamst_halts e')).
  { intros invG_inst' κs.
    iExists (fun σ _ => True%I).
    iExists (fun _ => True%I).
    iMod (gen_heap_init (∅ : gmap loc lamst.lang.val)) as (gen_heapG_inst') "(H∅ & _ & _)". iModIntro. iSplit; auto.
    iDestruct (Hee' Σ (lam_irisG_inst invG_inst') gen_heapG_inst' _ _) as "Hee'". clear Hee'. rewrite /exprel_typed /lift /=.
    iSpecialize ("Hee'" $! ∅ with "H∅").
    iApply (wp_wand with "Hee'").
    iIntros (w) "Hdes". iDestruct "Hdes" as (w' σ) "(_ & %He' & _)".
    iPureIntro. by exists w', σ.
  }
Qed.
