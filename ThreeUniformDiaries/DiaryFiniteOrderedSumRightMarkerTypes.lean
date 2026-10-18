import ThreeUniformDiaries.DiaryFiniteOrderedSumRightPairTransport
import ThreeUniformDiaries.DiaryProtectedMixedEdgeShapes

/-!
# Marker-cut singleton types and split-endpoint tests in finite sums

This file supplies the elementary nonleaf pieces needed to prove
exact full protected meets for arbitrary translated right vertices.

The induced right-copy embedding reflects every singleton test
below the three initial markers. Under E1--E5, a genuine 1/2-split
has no later incoming singleton tests at middle level >=3.
Consequently singleton types of two split endpoints are completely
determined by their first three marker tests.

A leaf and a split can never have the same singleton type through
marker cut three, because their marker role bits already differ.
These lemmas use neither S1/S2 nor a global RolePrediary on Nat.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Exact right-copy singleton agreement at every cut at most 3.
No role assumptions are required for either terminal vertex. -/
theorem finiteTwoBlockCarrier_right_oneType_marker_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (l u v : Nat) (hl : l ≤ 3) :
    ((finiteTwoBlockCarrier H K n m bits).SameOneTypeBelow
        l (rightBlockImage n u) (rightBlockImage n v) ↔
       K.SameOneTypeBelow l u v) := by
  constructor
  · intro ht a b hab hb
    have ha3 : a < 3 := by omega
    have hb3 : b < 3 := by omega
    have hFixA := rightBlockImage_marker n a ha3
    have hFixB := rightBlockImage_marker n b hb3
    have hu := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits a b u
    have hv := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits a b v
    rw [hFixA,hFixB] at hu hv
    exact hu.symm.trans ((ht (a := a) (b := b) hab hb).trans hv)
  · intro hs a b hab hb
    have ha3 : a < 3 := by omega
    have hb3 : b < 3 := by omega
    have hFixA := rightBlockImage_marker n a ha3
    have hFixB := rightBlockImage_marker n b hb3
    have hu := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits a b u
    have hv := finiteTwoBlockCarrier_right_edge_iff_all
      FH FK bits a b v
    rw [hFixA,hFixB] at hu hv
    exact hu.trans ((hs (a := a) (b := b) hab hb).trans hv.symm)

/-- For any E1--E5-shaped ternary graph, a split endpoint admits
no incoming singleton test with a nonmarker middle coordinate. -/
theorem E_split_no_late_singleton_test
    (hE : ∀ x y z : Nat, H.edge x y z → PermittedDiaryEdge H x y z)
    (a b z : Nat) (hz : IsDiarySplit H z) (hb : 3 ≤ b) :
    ¬ H.edge a b z := by
  have hNotLeaf : ¬ IsLeaf H z := hz.not_leaf
  intro he
  rcases hE a b z he with hMarker | hOne | hTwo | hDevlin | hNormal
  · rcases hMarker.2.1 with h | h <;> omega
  · exact hNotLeaf hOne.2.2
  · exact hNotLeaf hTwo.2.2
  · exact hNotLeaf hDevlin.2.2
  · exact hNotLeaf hNormal.2.2

/-- For genuine split endpoints, singleton-type agreement at any
cut >=3 reduces to agreement at the original three markers. -/
theorem E_split_oneType_stable
    (hE : ∀ x y z : Nat, H.edge x y z → PermittedDiaryEdge H x y z)
    (l u v : Nat) (hl : 3 ≤ l)
    (hu : IsDiarySplit H u) (hv : IsDiarySplit H v) :
    H.SameOneTypeBelow l u v ↔ H.SameOneTypeBelow 3 u v := by
  constructor
  · intro h a b hab hb
    exact h hab (by omega)
  · intro h a b hab hb
    by_cases hb3 : b < 3
    · exact h hab hb3
    · exact iff_of_false
        (E_split_no_late_singleton_test hE a b u hu (by omega))
        (E_split_no_late_singleton_test hE a b v hv (by omega))

/-- A leaf and a split have different marker singleton profiles.
This applies equally to a true finite source and to its carrier. -/
theorem leaf_split_not_sameOneType_three
    (G : Ordered3Graph Nat) (u v : Nat)
    (hu : IsLeaf G u) (hv : IsDiarySplit G v) :
    ¬ G.SameOneTypeBelow 3 u v := by
  intro h
  rcases hv with hOne | hTwo
  · have hEq := h (a := 0) (b := 1) (by omega) (by omega)
    exact hu.2.1 (hEq.mpr hOne.2.1)
  · have hEq := h (a := 0) (b := 2) (by omega) (by omega)
    exact hu.2.2 (hEq.mpr hTwo.2.2)

/-- The same marker exclusion with the split in the first slot. -/
theorem split_leaf_not_sameOneType_three
    (G : Ordered3Graph Nat) (u v : Nat)
    (hu : IsDiarySplit G u) (hv : IsLeaf G v) :
    ¬ G.SameOneTypeBelow 3 u v := by
  intro h
  rcases hu with hOne | hTwo
  · have hEq := h (a := 0) (b := 1) (by omega) (by omega)
    exact hv.2.1 (hEq.mp hOne.2.1)
  · have hEq := h (a := 0) (b := 2) (by omega) (by omega)
    exact hv.2.2 (hEq.mp hTwo.2.2)

end DiaryLeafPriority
end ThreeUniformDiaries
