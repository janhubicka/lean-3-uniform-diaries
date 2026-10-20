import ThreeUniformDiaries.DiaryFiniteSupportPermittedEdges
import ThreeUniformDiaries.DiaryFiniteLeafMeetS1Reduct
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex

/-!
# Finite leaf-meet reduction preserves both actual V3 Devlin markers

For any two selected finite leaves, source S1 makes their old
singleton meet a genuine one-split. This old split is retained
by the generated support, and its exact indexed singleton meet
was checked in the finite S1 proof.

The E-only LexEarlier lemma identifies the *source* and the
*finite induced target* lexicographic comparisons with the same
right split/leaf incidence, copied literally by inducedness.
The two Devlin marker edges are also copied literally, so both
V3 clauses follow. No claim about arbitrary mixed pair meets
or finite V-witnesses is needed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {L : Finset Nat}

/-- Full V3 on actual bounded leaf pairs in the finite generated
leaf-meet support, including BOTH complementary Devlin markers. -/
theorem finiteLeafMeetSupport_reindexed_V3
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (i j : Nat)
    (hij : i < j)
    (hj : j < (finiteLeafMeetSupport G L).card)
    (hiLeaf : IsLeaf
      (finiteSupportGraph G (finiteLeafMeetSupport G L)) i)
    (hjLeaf : IsLeaf
      (finiteSupportGraph G (finiteLeafMeetSupport G L)) j) :
    ((finiteSupportGraph G (finiteLeafMeetSupport G L)).edge 1 i j ↔
       LexEarlier
         (finiteSupportGraph G (finiteLeafMeetSupport G L)) i j) ∧
    ((finiteSupportGraph G (finiteLeafMeetSupport G L)).edge 2 i j ↔
       ¬ LexEarlier
         (finiteSupportGraph G (finiteLeafMeetSupport G L)) i j) := by
  classical
  let S := finiteLeafMeetSupport G L
  let H := finiteSupportGraph G S
  let A := finiteSupportIndex S i
  let B := finiteSupportIndex S j
  let m := G.oneMeetLevel A B
  have hi : i < S.card := lt_trans hij hj
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  have hOldLeafI : IsLeaf G A :=
    (finiteSupportGraph_leaf_iff
      (G := G) (S := S) h0 h1 h2 i hiLeaf.1 hi).mp hiLeaf
  have hOldLeafJ : IsLeaf G B :=
    (finiteSupportGraph_leaf_iff
      (G := G) (S := S) h0 h1 h2 j hjLeaf.1 hj).mp hjLeaf
  have hAi : A ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L
      D hLeaves i hiLeaf.1 hi hiLeaf
  have hBj : B ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L
      D hLeaves j hjLeaf.1 hj hjLeaf
  have hAB : A < B := finiteSupportIndex_strictMono S i j hij hj
  have hSourceSplit : IsOneSplit G m :=
    D.singleton_meets A B hOldLeafI hOldLeafJ (ne_of_lt hAB)
  have hmMem : m ∈ S :=
    mem_finiteLeafMeetSupport_oneMeet
      G L A B hAi hBj (ne_of_lt hAB)
  obtain ⟨k,hk,hkm⟩ := finiteSupportIndex_surjective_on S m hmMem
  have hk3 : 3 ≤ k :=
    finiteSupportIndex_ge_three_of_image S k h0 h1 h2 hk
      (by simpa only [hkm] using hSourceSplit.1)
  have hmBound : m ≤ min A B := G.oneMeetLevel_le_min A B
  have hmA : m < A := by
    have hle : m ≤ A := hmBound.trans (min_le_left _ _)
    have hne : m ≠ A := by
      intro h
      have hs : IsOneSplit G A := by
        simpa only [h] using hSourceSplit
      exact hOldLeafI.2.1 hs.2.1
    omega
  have hmB : m < B := by
    have hle : m ≤ B := hmBound.trans (min_le_right _ _)
    have hne : m ≠ B := by
      intro h
      have hs : IsOneSplit G B := by
        simpa only [h] using hSourceSplit
      exact hOldLeafJ.2.1 hs.2.1
    omega
  have hki : k < i := finiteSupportIndex_lt_of_image_lt
    S k i hk hi (by simpa only [hkm] using hmA)
  have hkj : k < j := finiteSupportIndex_lt_of_image_lt
    S k j hk hj (by simpa only [hkm] using hmB)
  have hTargetSplit : IsOneSplit H k :=
    (finiteSupportGraph_oneSplit_iff
      (G := G) (S := S) h0 h1 h2 k hk3 hk).mpr
        (by simpa only [hkm] using hSourceSplit)
  have hTargetMeet : H.oneMeetLevel i j = k :=
    finiteSupportGraph_oneMeet_exact_at_retained_oneSplit
      D h0 h1 h2 i j k A B m
      hi hj hk hij hk3 hki hkj rfl rfl hkm hSourceSplit rfl
  have hTargetLex : LexEarlier H i j ↔ H.edge 0 k j :=
    E_oneSplit_lexEarlier_iff_right
      (finiteSupportGraph_permitted_edge D h0 h1 h2)
      k i j hTargetSplit hij hki hTargetMeet
  have hSourceLex : LexEarlier G A B ↔ G.edge 0 m B :=
    E_oneSplit_lexEarlier_iff_right
      D.permitted_edge m A B hSourceSplit hAB hmA rfl
  obtain ⟨_,hZero,hOne,hTwo⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  have hSplitEdge : H.edge 0 k j ↔ G.edge 0 m B := by
    have h := finiteSupportGraph_edge_iff G S 0 k j
      (by omega) hkj hj
    simpa only [hZero,hkm] using h
  have hLex : LexEarlier H i j ↔ LexEarlier G A B :=
    hTargetLex.trans (hSplitEdge.trans hSourceLex.symm)
  have hMarkerOne : H.edge 1 i j ↔ G.edge 1 A B := by
    have h := finiteSupportGraph_edge_iff G S 1 i j
      (by omega) hij hj
    simpa only [hOne] using h
  have hMarkerTwo : H.edge 2 i j ↔ G.edge 2 A B := by
    have h := finiteSupportGraph_edge_iff G S 2 i j
      (by omega) hij hj
    simpa only [hTwo] using h
  constructor
  · exact hMarkerOne.trans
      ((D.leaf_marker_one A B hAB hOldLeafI hOldLeafJ).trans hLex.symm)
  · exact hMarkerTwo.trans
      ((D.leaf_marker_two A B hAB hOldLeafI hOldLeafJ).trans
        (not_congr hLex.symm))

end DiaryLeafPriority
end ThreeUniformDiaries
