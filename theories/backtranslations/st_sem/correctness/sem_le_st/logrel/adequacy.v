From iris.base_logic.lib Require Import invariants gen_heap wsat ghost_map.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.
From st.STLCmuST Require Import lang types.
From st.STLCmuVS Require Import wkpre lang.
From st.backtranslations.st_sem.correctness.sem_le_st.logrel Require Import definition lift.
From st Require Import resources.

Definition Σ : gFunctors :=
  #[invΣ;
    gen_heapΣ loc STLCmuST.lang.val;
    ghost_mapΣ nat STLCmuVS.lang.val;
    ghost_mapΣ nat loc
    ].

Instance STLCmuVS_irisGS_inst (H : invGS Σ) : irisGS STLCmuVS_lang Σ :=
  { iris_invG := H;
    state_interp σ _ κs _ := True%I;
    fork_post v := True%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _;
  }.

Instance sem_le_stΣ_inst (H : invGS Σ) (H' : gen_heapGS loc lang.val Σ) : sem_le_stΣ Σ :=
  { irisGS_inst' := _ ;
    genHeapG_inst := _;
    val_ghost_mapG_inst := _;
    loc_ghost_mapG_inst := _;
  }.


Lemma exprel_adequate (e : expr) (e' : STLCmuST.lang.expr)
      (Hee' : ∀ {Σ : gFunctors}
                {semΣ_inst : sem_le_stΣ Σ},
          ⊢ exprel_typed [] TUnit e e') :
  STLCmuVS_halts e → STLCmuST_halts e'.
Proof.
  intros He. destruct He as (v & He).
  cut (adequate MaybeStuck e tt (fun _ _ => STLCmuST_halts e')).
  { intro Ha. apply (adequate_result _ _ _ _ Ha [] tt v).
    change ([?e], ?σ) with ((fun x => ([x], tt)) e).
    eapply (rtc_congruence (fun x => ([x], tt))); eauto.
    intros e1 e2 Hstep. rewrite /STLCmuVS_step in Hstep.
    rewrite /erased_step /=. exists []. apply (step_atomic e1 tt e2 tt [] [] []); by simpl. }
  apply (wp_adequacy Σ STLCmuVS_lang MaybeStuck e tt (fun _ => STLCmuST_halts e')).
  { intros invGS_inst' κs.
    iExists (fun σ _ => True%I).
    iExists (fun _ => True%I).
    iMod (gen_heap_init (∅ : gmap loc STLCmuST.lang.val)) as (gen_heapGS_inst') "(H∅ & _ & _)". iModIntro. iSplit; auto.
    iDestruct (Hee' Σ _ ) as "Hee'". clear Hee'. rewrite /exprel_typed /lift /=.
    iSpecialize ("Hee'" $! ∅ with "H∅").
    iApply (wp_wand with "Hee'").
    iIntros (w) "Hdes". iDestruct "Hdes" as (w' σ) "(_ & %He' & _)".
    iPureIntro. by exists w', σ.
  }
Qed.
