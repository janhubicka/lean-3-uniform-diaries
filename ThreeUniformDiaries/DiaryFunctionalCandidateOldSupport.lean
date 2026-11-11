import ThreeUniformDiaries.DiaryFiniteCandidateCriterion

/-!
# Track A: functional new-leaf generator tables already freeze the old support

The candidate generator relation contains markers, every selected old
leaf, and all S1/S2 meet-generator rows from the old selected leaves.
The proposed next-leaf image v changes NONE of those old leaf rows.

If the whole proposed generator relation is functional, every OLD
generator value is therefore forced to be exactly its already certified
value under the old admissible map f. This proves agreement on the
ENTIRE S_m support without assuming that the candidate map is a
genuine admissible next stage or checking roles, edges/nonedges,
order, range membership, or future reserve.

This is a strictly finite algebraic simplification of the relative
candidate test. It asserts neither functionality of a proposed
candidate nor existence of any protected target leaf.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A functional proposed new-leaf generator table automatically agrees
with the genuine old admissible diary map on every vertex of the OLD
leaf-meet support, including marker vertices and all S1/S2 generators.

No RoleDiary assumption on H or K is needed beyond the actual old
stage P; in particular, no proposed new stage and no candidate roles
or E2/E3 incidences are assumed. -/
theorem AdmissibleCofinalDiaryStage.functional_candidate_table_preserves_old_support
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hFunctional : FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f v)) :
    ∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
      candidateNewLeafTableMap H K m f v u = f u := by
  classical
  let Lold := countableDiaryLeafPrefix H m
  let L := countableDiaryLeafPrefix H (m + 1)
  let q := candidateLeafImage f m v
  let T := candidateNewLeafGeneratorTable H K m f v
  have hOldLeafIncluded (a : Nat) (ha : a ∈ Lold) : a ∈ L :=
    (countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) ha
  have hOldLeafVal (a : Nat) (ha : a ∈ Lold) : q a = f a := by
    have haLt : a < m :=
      ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.1
    simp [q, candidateLeafImage, ne_of_lt haLt]
  have hOldLeafRole (a : Nat) (ha : a ∈ Lold) : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  have hOldSupported (a : Nat) (ha : a ∈ Lold) :
      a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H Lold a ha
  have hValue (x y : Nat) (hRow : (x,y) ∈ T) :
      candidateNewLeafTableMap H K m f v x = y := by
    change finiteGeneratorTableValue T x = y
    exact finiteGeneratorTableValue_eq_of_mem T hFunctional x y hRow
  intro u hu
  change u ∈ (Finset.range 3 ∪ Lold) ∪
    (finiteOneMeetSupport H Lold ∪ finiteTwoMeetSupport H Lold) at hu
  rcases Finset.mem_union.mp hu with hMarkerOrLeaf | hMeet
  · rcases Finset.mem_union.mp hMarkerOrLeaf with hMarker | hLeaf
    · have huSmall : u < 3 := Finset.mem_range.mp hMarker
      have hCases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
      rcases hCases with rfl | rfl | rfl
      · exact (hValue 0 0
          (finiteLeafGeneratorTable_marker H K L q 0 (by omega))).trans
            P.marker_zero.symm
      · exact (hValue 1 1
          (finiteLeafGeneratorTable_marker H K L q 1 (by omega))).trans
            P.marker_one.symm
      · exact (hValue 2 2
          (finiteLeafGeneratorTable_marker H K L q 2 (by omega))).trans
            P.marker_two.symm
    · exact (hValue u (q u)
        (finiteLeafGeneratorTable_leaf H K L q u
          (hOldLeafIncluded u hLeaf))).trans
        (hOldLeafVal u hLeaf)
  · rcases Finset.mem_union.mp hMeet with hOne | hTwo
    · change u ∈ ((Lold.product Lold).filter
        (fun p : Nat × Nat => p.1 ≠ p.2)).image
          (fun p : Nat × Nat => H.oneMeetLevel p.1 p.2) at hOne
      obtain ⟨⟨a,b⟩,hPair,hEq⟩ := Finset.mem_image.mp hOne
      obtain ⟨hPair,hNe⟩ := Finset.mem_filter.mp hPair
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hPair
      have hRow :
          (H.oneMeetLevel a b,
            K.oneMeetLevel (q a) (q b)) ∈ T :=
        finiteLeafGeneratorTable_oneMeet H K L q a b
          (hOldLeafIncluded a ha) (hOldLeafIncluded b hb) hNe
      calc
        candidateNewLeafTableMap H K m f v u =
            candidateNewLeafTableMap H K m f v
              (H.oneMeetLevel a b) := by rw [hEq]
        _ = K.oneMeetLevel (q a) (q b) := hValue _ _ hRow
        _ = K.oneMeetLevel (f a) (f b) := by
          rw [hOldLeafVal a ha, hOldLeafVal b hb]
        _ = f (H.oneMeetLevel a b) :=
          (P.leaf_oneMeet a b
            (hOldSupported a ha) (hOldSupported b hb)
            (hOldLeafRole a ha) (hOldLeafRole b hb)).symm
        _ = f u := congrArg f hEq
    · change u ∈
        ((finiteOrderedLeafPairs Lold).product
          (finiteOrderedLeafPairs Lold)).image
          (fun p : (Nat × Nat) × (Nat × Nat) =>
            H.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2) at hTwo
      obtain ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,hp,hEq⟩ :=
        Finset.mem_image.mp hTwo
      obtain ⟨hAB,hCD⟩ := Finset.mem_product.mp hp
      obtain ⟨hAB,hab⟩ := Finset.mem_filter.mp hAB
      obtain ⟨hCD,hcd⟩ := Finset.mem_filter.mp hCD
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hAB
      obtain ⟨hc,hd⟩ := Finset.mem_product.mp hCD
      have hRow :
          (H.twoMeetLevel a b c d,
            K.twoMeetLevel (q a) (q b) (q c) (q d)) ∈ T :=
        finiteLeafGeneratorTable_twoMeet H K L q a b c d
          (hOldLeafIncluded a ha) (hOldLeafIncluded b hb)
          (hOldLeafIncluded c hc) (hOldLeafIncluded d hd)
          hab hcd
      calc
        candidateNewLeafTableMap H K m f v u =
            candidateNewLeafTableMap H K m f v
              (H.twoMeetLevel a b c d) := by rw [hEq]
        _ = K.twoMeetLevel (q a) (q b) (q c) (q d) :=
          hValue _ _ hRow
        _ = K.twoMeetLevel (f a) (f b) (f c) (f d) := by
          rw [hOldLeafVal a ha, hOldLeafVal b hb,
            hOldLeafVal c hc, hOldLeafVal d hd]
        _ = f (H.twoMeetLevel a b c d) :=
          (P.leaf_twoMeet a b c d
            (hOldSupported a ha) (hOldSupported b hb)
            (hOldSupported c hc) (hOldSupported d hd)
            hab hcd
            (hOldLeafRole a ha) (hOldLeafRole b hb)
            (hOldLeafRole c hc) (hOldLeafRole d hd)).symm
        _ = f u := congrArg f hEq

/-- In particular the functionality field of the existing precise
finite-candidate predicate already freezes the old support: none of
its other order/role/edge/leaf-range tests is used for this fact. -/
theorem FiniteNewLeafCandidateCondition.table_old_support_eq
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (C : FiniteNewLeafCandidateCondition H K F m f v) :
    ∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
      candidateNewLeafTableMap H K m f v u = f u :=
  P.functional_candidate_table_preserves_old_support C.functional

end DiaryLeafPriority
end ThreeUniformDiaries
