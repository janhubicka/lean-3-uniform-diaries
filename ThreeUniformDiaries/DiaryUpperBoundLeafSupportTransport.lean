import ThreeUniformDiaries.DiaryFiniteLeafMeetS2Reduct

/-!
# Track A: exact selected-leaf meet transport under diary support compression

The existing leaf-meet closure proofs show that a selected finite
support is a full finite RoleDiary. Their internal S1/S2 arguments
actually establish MORE: numerical singleton and full ordered-pair
meets of every selected leaf (respectively leaf pair) are transported
EXACTLY by the increasing induced support enumeration.

We expose those exact transport equalities for the upper-bound
marked-envelope factorisation. This is not yet full finite ATR:
mixed split/leaf comparisons and auxiliary meets still require
the marker/small-or-cap analysis, followed by the existing
FiniteAuxEmbedding.of_exact_meets theorem. No countable fusion
or diary Ramsey theorem is used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {L : Finset Nat}

/-- Retaining the genuine S1 witness gives exact NUMERICAL
singleton-meet transport, not merely the compressed S1 role.
Both selected leaves may be separated by arbitrarily many
omitted ambient vertices. -/
theorem finiteLeafMeetSupport_selected_oneMeet_transport
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (i j : Nat)
    (hi : i < (finiteLeafMeetSupport G L).card)
    (hj : j < (finiteLeafMeetSupport G L).card)
    (hij : i < j)
    (hUi : finiteSupportIndex (finiteLeafMeetSupport G L) i ∈ L)
    (hVj : finiteSupportIndex (finiteLeafMeetSupport G L) j ∈ L) :
    G.oneMeetLevel
      (finiteSupportIndex (finiteLeafMeetSupport G L) i)
      (finiteSupportIndex (finiteLeafMeetSupport G L) j) =
    finiteSupportIndex (finiteLeafMeetSupport G L)
      ((finiteSupportGraph G (finiteLeafMeetSupport G L)).oneMeetLevel i j) := by
  classical
  let S := finiteLeafMeetSupport G L
  let H := finiteSupportGraph G S
  let u := finiteSupportIndex S i
  let v := finiteSupportIndex S j
  let m := G.oneMeetLevel u v
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  have huLeaf : IsLeaf G u := hLeaves u hUi
  have hvLeaf : IsLeaf G v := hLeaves v hVj
  have huv : u < v := finiteSupportIndex_strictMono S i j hij hj
  have hSourceSplit : IsOneSplit G m :=
    D.singleton_meets u v huLeaf hvLeaf (ne_of_lt huv)
  have hmMem : m ∈ S :=
    mem_finiteLeafMeetSupport_oneMeet G L u v hUi hVj (ne_of_lt huv)
  obtain ⟨k,hk,hkm⟩ := finiteSupportIndex_surjective_on S m hmMem
  have hk3 : 3 ≤ k :=
    finiteSupportIndex_ge_three_of_image S k h0 h1 h2 hk
      (by simpa only [hkm] using hSourceSplit.1)
  have hmBound : m ≤ min u v := G.oneMeetLevel_le_min u v
  have hmu : m < u := by
    have hle : m ≤ u := hmBound.trans (min_le_left _ _)
    have hne : m ≠ u := by
      intro h
      have hOne : IsOneSplit G u := by
        simpa only [h] using hSourceSplit
      exact huLeaf.2.1 hOne.2.1
    omega
  have hmv : m < v := by
    have hle : m ≤ v := hmBound.trans (min_le_right _ _)
    have hne : m ≠ v := by
      intro h
      have hOne : IsOneSplit G v := by
        simpa only [h] using hSourceSplit
      exact hvLeaf.2.1 hOne.2.1
    omega
  have hki : k < i := finiteSupportIndex_lt_of_image_lt
    S k i hk hi (by simpa only [hkm] using hmu)
  have hkj : k < j := finiteSupportIndex_lt_of_image_lt
    S k j hk hj (by simpa only [hkm] using hmv)
  have hExact : H.oneMeetLevel i j = k :=
    finiteSupportGraph_oneMeet_exact_at_retained_oneSplit
      D h0 h1 h2 i j k u v m hi hj hk
      hij hk3 hki hkj rfl rfl hkm hSourceSplit rfl
  change m = finiteSupportIndex S (H.oneMeetLevel i j)
  rw [hExact]
  exact hkm.symm

/-- Exact full ordered-pair meet transport for any TWO ordered
pairs of selected genuine diary leaves. The three possible
source cases are marker 1, 2-split, and capped first coordinate.
This is stronger than the disjunction in the S2 conclusion. -/
theorem finiteLeafMeetSupport_leafPair_twoMeet_transport
    (D : RoleDiary G)
    (hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u)
    (i j p q : Nat)
    (hi : i < (finiteLeafMeetSupport G L).card)
    (hj : j < (finiteLeafMeetSupport G L).card)
    (hp : p < (finiteLeafMeetSupport G L).card)
    (hq : q < (finiteLeafMeetSupport G L).card)
    (hij : i < j) (hpq : p < q)
    (hiLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) i)
    (hjLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) j)
    (hpLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) p)
    (hqLeaf : IsLeaf (finiteSupportGraph G (finiteLeafMeetSupport G L)) q) :
    G.twoMeetLevel
      (finiteSupportIndex (finiteLeafMeetSupport G L) i)
      (finiteSupportIndex (finiteLeafMeetSupport G L) j)
      (finiteSupportIndex (finiteLeafMeetSupport G L) p)
      (finiteSupportIndex (finiteLeafMeetSupport G L) q) =
    finiteSupportIndex (finiteLeafMeetSupport G L)
      ((finiteSupportGraph G (finiteLeafMeetSupport G L)).twoMeetLevel i j p q) := by
  classical
  let S := finiteLeafMeetSupport G L
  let H := finiteSupportGraph G S
  let A := finiteSupportIndex S i
  let B := finiteSupportIndex S j
  let C := finiteSupportIndex S p
  let E := finiteSupportIndex S q
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker G L 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker G L 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker G L 2 (by omega)
  have hAi : A ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L D hLeaves
      i hiLeaf.1 hi hiLeaf
  have hBj : B ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L D hLeaves
      j hjLeaf.1 hj hjLeaf
  have hCp : C ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L D hLeaves
      p hpLeaf.1 hp hpLeaf
  have hEq : E ∈ L :=
    finiteLeafMeetSupport_reindexed_leaf_mem_L D hLeaves
      q hqLeaf.1 hq hqLeaf
  have hALeaf : IsLeaf G A := hLeaves A hAi
  have hBLeaf : IsLeaf G B := hLeaves B hBj
  have hCLeaf : IsLeaf G C := hLeaves C hCp
  have hELeaf : IsLeaf G E := hLeaves E hEq
  have hAB : A < B := finiteSupportIndex_strictMono S i j hij hj
  have hCE : C < E := finiteSupportIndex_strictMono S p q hpq hq
  let m := G.twoMeetLevel A B C E
  rcases D.pair_meets A B C E hAB hCE
      hALeaf hBLeaf hCLeaf hELeaf with hCap | hMarker | hSplit
  · have hCapIndex :
        G.twoMeetLevel A B C E = finiteSupportIndex S (min i p) := by
      rw [hCap]
      exact (finiteSupportIndex_min_below S i p hi hp).symm
    have hExact : H.twoMeetLevel i j p q = min i p :=
      finiteSupportGraph_capped_twoMeet_exact
        (G := G) (S := S) i j p q hi hj hp hq hij hpq hCapIndex
    change G.twoMeetLevel A B C E =
      finiteSupportIndex S (H.twoMeetLevel i j p q)
    rw [hExact]
    exact hCapIndex
  · have hExact : H.twoMeetLevel i j p q = 1 :=
      finiteSupportGraph_twoMeet_exact_at_marker_one
        D h0 h1 h2 i j p q hi hj hp hq hij hpq
        hiLeaf.1 hpLeaf.1 hALeaf hBLeaf hCLeaf hELeaf hMarker
    have hIdx1 : finiteSupportIndex S 1 = 1 :=
      (finiteSupportIndex_initial_markers S h0 h1 h2).2.2.1
    change G.twoMeetLevel A B C E =
      finiteSupportIndex S (H.twoMeetLevel i j p q)
    rw [hMarker, hExact, hIdx1]
  · have hmMem : m ∈ S :=
      mem_finiteLeafMeetSupport_twoMeet G L
        A B C E hAB hCE hAi hBj hCp hEq
    obtain ⟨k,hk,hkm⟩ := finiteSupportIndex_surjective_on S m hmMem
    have hSplitM : IsTwoSplit G m := hSplit
    have hk3 : 3 ≤ k :=
      finiteSupportIndex_ge_three_of_image S k h0 h1 h2 hk
        (by simpa only [hkm] using hSplitM.1)
    have hmBound : m ≤ min A C := G.twoMeetLevel_le_min A B C E
    have hma : m < A := by
      have hle := hmBound.trans (min_le_left _ _)
      have hne : m ≠ A := by
        intro h
        have hSplitA : IsTwoSplit G A := by
          simpa only [h] using hSplitM
        exact hALeaf.2.2 hSplitA.2.2
      omega
    have hmc : m < C := by
      have hle := hmBound.trans (min_le_right _ _)
      have hne : m ≠ C := by
        intro h
        have hSplitC : IsTwoSplit G C := by
          simpa only [h] using hSplitM
        exact hCLeaf.2.2 hSplitC.2.2
      omega
    have hki : k < i :=
      finiteSupportIndex_lt_of_image_lt S k i hk hi
        (by simpa only [hkm] using hma)
    have hkp : k < p :=
      finiteSupportIndex_lt_of_image_lt S k p hk hp
        (by simpa only [hkm] using hmc)
    have hExact : H.twoMeetLevel i j p q = k :=
      finiteSupportGraph_twoMeet_exact_at_retained_twoSplit
        D i j p q k hi hj hp hq hk hij hpq hki hkp
        (by simpa only [hkm] using hSplitM)
        (by simpa only [hkm] using (show
          G.twoMeetLevel A B C E = m from rfl))
    change G.twoMeetLevel A B C E =
      finiteSupportIndex S (H.twoMeetLevel i j p q)
    rw [hExact]
    exact hkm.symm

end DiaryLeafPriority
end ThreeUniformDiaries
