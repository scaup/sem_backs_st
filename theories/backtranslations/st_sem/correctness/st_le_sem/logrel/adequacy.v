From iris.base_logic.lib Require Import invariants gen_heap wsat ghost_map.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants gen_heap.
From st.STLCmuVS Require Import lang.
From st.STLCmuST Require Import wkpre lang types.
From st.backtranslations.st_sem.correctness.st_le_sem.logrel Require Import definition lift.
From st Require Import resources.

Definition Σ : gFunctors :=
  #[invΣ;
    gen_heapΣ loc val;
    ghost_mapΣ nat STLCmuVS.lang.val;
    ghost_mapΣ nat loc
    ].

Instance st_le_semΣ_inst (H : invGS Σ) (H' : gen_heapGS loc lang.val Σ) : st_le_semΣ Σ :=
  { invGS_inst := _ ;
    genHeapG_inst' := _;
    val_ghost_mapG_inst' := _;
    loc_ghost_mapG_inst' := _;
  }.

(* st_le_ *)
Lemma exprel_adequate (e : expr) (e' : STLCmuVS.lang.expr)
      (Hee' : ∀ {Σ : gFunctors}
                {st_le_semΣ_inst : st_le_semΣ Σ},
          ⊢ exprel_typed [] TUnit e e') :
  STLCmuST_halts e → STLCmuVS_halts e'.
Proof.
  intros He. destruct He as (v & σ & He).
  cut (adequate MaybeStuck e ∅ (fun _ _ => STLCmuVS_halts e')).
  { intro Ha. apply (adequate_result _ _ _ _ Ha [] σ v).
    change ([?e], ?σ) with ((fun p => ([p.2], p.1)) (σ, e)).
    eapply (rtc_congruence (fun p => ([p.2], p.1))); eauto.
    intros [σ1 e1] [σ2 e2] Hstep. rewrite /STLCmuST_step in Hstep.
    rewrite /erased_step /=. exists []. apply (step_atomic e1 σ1 e2 σ2 [] [] []); by simpl. }
  apply (wp_adequacy Σ STLCmuST_lang MaybeStuck e (∅ : gmap loc val) (fun _ => STLCmuVS_halts e')).
  { intros invGS_inst' κs.
    iMod (gen_heap_init (∅ : gmap loc val)) as (gen_heapGS_inst') "(H∅ & _ & _)". iModIntro.
    iExists (fun σ _ => gen_heap_interp σ).
    iExists (fun _ => True%I).
    iFrame "H∅".
    specialize (Hee' Σ _).
    iDestruct Hee' as "Hee'". rewrite /exprel_typed /lift /=.
    iApply (wp_wand with "Hee'").
    iIntros (w) "Hdes". iDestruct "Hdes" as (w') "[%He' _]".
    iPureIntro. by eexists.
  }
Qed.

