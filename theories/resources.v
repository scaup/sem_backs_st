From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris Require Import program_logic.weakestpre.
From st.lam Require lang.
From st.lamst Require lang.

Class semΣ Σ := { irisG_inst :> irisG lam.lang.lam_lang Σ;
                  ghost_mapG_inst :> ghost_mapG Σ nat (prod lam.lang.val lam.lang.val)
                }.

Class sem_le_stΣ Σ := { irisG_inst' :> irisG lam.lang.lam_lang Σ;
                        genHeapG_inst :> gen_heapG lamst.lang.loc lamst.lang.val Σ ;
                        val_ghost_mapG_inst :> ghost_mapG Σ nat lam.lang.val ;
                        loc_ghost_mapG_inst :> ghost_mapG Σ nat lamst.lang.loc
                      }.

Global Instance lamst_irisG_instance `{H : invG Σ} {H' : gen_heapG lamst.lang.loc lamst.lang.val Σ} : irisG lamst.lang.lamst_lang Σ :=
  { iris_invG := H;
    state_interp σ _ κs _ := gen_heap_interp σ;
    fork_post v := True%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  }.

Class st_le_semΣ Σ := { invG_inst :> invG Σ;
                        genHeapG_inst' :> gen_heapG lamst.lang.loc lamst.lang.val Σ;
                        val_ghost_mapG_inst' :> ghost_mapG Σ nat lam.lang.val;
                        loc_ghost_mapG_inst' :> ghost_mapG Σ nat lamst.lang.loc
                      }.
