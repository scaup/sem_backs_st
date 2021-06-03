From iris.base_logic.lib Require Import invariants gen_heap wsat ghost_map.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.
From st.lam Require Import lang.
From st.lamst Require Import wkpre lang types.
From st.backtranslations.st_sem.correctness.st_le_sem.logrel Require Import definition lift.

Definition Σ : gFunctors :=
  #[invΣ;
    gen_heapΣ loc val;
    ghost_mapΣ nat lam.lang.val;
    ghost_mapΣ nat loc
    ].

Lemma exprel_adequate (e : expr) (e' : lam.lang.expr)
      (Hee' : ∀ {Σ : gFunctors}
                {invG_inst : invG Σ}
                {genHeapG_inst : gen_heapG loc val Σ}
                {val_ghost_mapG_inst : ghost_mapG Σ nat lam.lang.val}
                {loc_ghost_mapG_inst : ghost_mapG Σ nat loc},
          ⊢ exprel_typed [] TUnit e e') :
  lamst_halts e → lam_halts e'.
Proof.
  intros He. destruct He as (v & σ & He).
  cut (adequate MaybeStuck e ∅ (fun _ _ => lam_halts e')).
  { intro Ha. apply (adequate_result _ _ _ _ Ha [] σ v).
    change ([?e], ?σ) with ((fun p => ([p.2], p.1)) (σ, e)).
    eapply (rtc_congruence (fun p => ([p.2], p.1))); eauto.
    intros [σ1 e1] [σ2 e2] Hstep. rewrite /lamst_step in Hstep.
    rewrite /erased_step /=. exists []. apply (step_atomic e1 σ1 e2 σ2 [] [] []); by simpl. }
  apply (wp_adequacy Σ lamst_lang MaybeStuck e (∅ : gmap loc val) (fun _ => lam_halts e')).
  { intros invG_inst' κs.
    iMod (gen_heap_init (∅ : gmap loc val)) as (gen_heapG_inst') "(H∅ & _ & _)". iModIntro.
    iExists (fun σ _ => gen_heap_interp σ).
    iExists (fun _ => True%I).
    iFrame "H∅".
    specialize (Hee' Σ invG_inst' gen_heapG_inst' _ _).
    iDestruct Hee' as "Hee'". rewrite /exprel_typed /lift /=.
    iApply (wp_wand with "Hee'").
    iIntros (w) "Hdes". iDestruct "Hdes" as (w') "[%He' _]".
    iPureIntro. by eexists.
  }
Qed.

