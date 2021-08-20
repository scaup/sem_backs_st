From st.STLCmuVS Require Import lang tactics lib.fixarrow.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import tactics.

Section list_gmap.

  Context {V : Type}.

  Definition list_gmap (ls : list V) : gmap nat V := map_seq 0 ls.

  Lemma list_gmap_lookup ls i : ls !! i = list_gmap ls !! i.
  Proof. rewrite /list_gmap. by rewrite lookup_map_seq_0. Qed.

  Lemma list_gmap_snoc ls l : list_gmap (ls ++ [l]) = <[ length ls := l ]> (list_gmap ls).
  Proof. by rewrite /list_gmap map_seq_snoc. Qed.

  Lemma list_gmap_insert ls l l' i (H : ls !! i = Some l) :
    list_gmap (<[i := l']> ls) = <[i := l']> (list_gmap ls).
  Proof.
    rewrite /list_gmap.
    rewrite -(take_drop_middle ls i l H).
    (* rewrite left side *)
    assert (i < length ls). by eapply lookup_lt_Some.
    assert (i = length (take i ls) + 0).
    { rewrite take_length_le; lia. }
    assert (map_seq 0 (<[i:=l']> (take i ls ++ l :: drop (S i) ls)) =
            map_seq 0 (<[(length (take i ls) + 0):=l']> (take i ls ++ l :: drop (S i) ls))
           ) as ->. by rewrite -H1.
    rewrite insert_app_r. simpl.
    (* both sides *)
    rewrite !map_seq_app.
    (* right side *)
    rewrite insert_union_r. 2: rewrite lookup_map_seq_0; apply lookup_take_ge; lia.
    (* simpl *)
    rewrite take_length_le; try by lia. change (0 + i) with i.
    (* both sides *)
    change (l' :: drop (S i) ls) with ([l'] ++ drop (S i) ls).
    change (l :: drop (S i) ls) with ([l] ++ drop (S i) ls).
    rewrite !map_seq_app.
    simpl.
    (* rigth side *)
    rewrite insert_union_l !insert_empty insert_singleton.
    done.
  Qed.

End list_gmap.
