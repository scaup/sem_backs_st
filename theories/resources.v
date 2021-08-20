From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris Require Import program_logic.weakestpre.
From st.STLCmuVS Require lang.
From st.STLCmuST Require lang.

Class semΣ Σ := { irisG_inst :> irisG STLCmuVS.lang.STLCmuVS_lang Σ;
                  ghost_mapG_inst :> ghost_mapG Σ nat (prod STLCmuVS.lang.val STLCmuVS.lang.val)
                }.

Class sem_le_stΣ Σ := { irisG_inst' :> irisG STLCmuVS.lang.STLCmuVS_lang Σ;
                        genHeapG_inst :> gen_heapG STLCmuST.lang.loc STLCmuST.lang.val Σ ;
                        val_ghost_mapG_inst :> ghost_mapG Σ nat STLCmuVS.lang.val ;
                        loc_ghost_mapG_inst :> ghost_mapG Σ nat STLCmuST.lang.loc
                      }.

Global Instance STLCmuST_irisG_instance `{H : invG Σ} {H' : gen_heapG STLCmuST.lang.loc STLCmuST.lang.val Σ} : irisG STLCmuST.lang.STLCmuST_lang Σ :=
  { iris_invG := H;
    state_interp σ _ κs _ := gen_heap_interp σ;
    fork_post v := True%I;
    num_laters_per_step _ := 0;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  }.

Class st_le_semΣ Σ := { invG_inst :> invG Σ;
                        genHeapG_inst' :> gen_heapG STLCmuST.lang.loc STLCmuST.lang.val Σ;
                        val_ghost_mapG_inst' :> ghost_mapG Σ nat STLCmuVS.lang.val;
                        loc_ghost_mapG_inst' :> ghost_mapG Σ nat STLCmuST.lang.loc
                      }.
