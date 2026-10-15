import ThreeUniformDiaries.DiaryFlipCrossBranchExtension

/-!
# Completing the missing Devlin marker edges for incomparable flip leaves

The induced union of flip branches omits both marker edges
(1,u,v), (2,u,v) for any pair of incomparable leaf nodes.
This module gives an explicit *safe* way to add exactly one,
determined by an arbitrary orientation choice on such pairs.

The three original markers are common to all flip branches,
and added edges are guarded by non-membership in every branch
and strictly increasing source levels. Hence every original
flip copy remains induced. An off-branch leaf pair receives
exactly one of its two Devlin markers.

IMPORTANT: An arbitrary orientation is not necessarily the
lexicographic order derived from the completed 1-type tree.
The full V1/V2/V3 coherence, meet preservation and pre-diary
claim are NOT established here. The result isolates the
previously missing pairwise marker existence condition.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary
namespace FlipFamily

variable {A : Ordered3Graph Nat} {ι : Type*}

/-- An ordered pair of nodes lies on one common flip branch. -/
def SharedBranchPair (T : FlipFamily A ι)
    (Y Z : FlipNode) : Prop :=
  ∃ (i : ι) (y z : Nat),
    y < z ∧ T.node i y = Y ∧ T.node i z = Z

/-- Increasing leaf nodes on different flip branches,
never simultaneously occurring in a single flip. -/
def OffBranchLeafPair (T : FlipFamily A ι)
    (Y Z : FlipNode) : Prop :=
  IsLeaf A Y.1 ∧ IsLeaf A Z.1 ∧
  Y.1 < Z.1 ∧ ¬ T.SharedBranchPair Y Z

theorem no_shared_pair_no_span
    (T : FlipFamily A ι) (Y Z X : FlipNode)
    (hn : ¬ T.SharedBranchPair Y Z) :
    ¬ T.BranchSpansTriple X Y Z := by
  rintro ⟨i, x, y, z, hxy, hyz, hx, hy, hz⟩
  exact hn ⟨i, y, z, hyz, hy, hz⟩

theorem no_shared_pair_no_raw_edge
    (T : FlipFamily A ι) (Y Z X : FlipNode)
    (hn : ¬ T.SharedBranchPair Y Z) :
    ¬ (T.branchAmalgam).edge X Y Z := by
  rintro ⟨i, x, y, z, hxy, hyz, hx, hy, hz, hedge⟩
  exact hn ⟨i, y, z, hyz, hy, hz⟩

/-- New marker edges only, labelled by the chosen orientation. -/
def crossMarkerExtra
    (T : FlipFamily A ι) (base : ι)
    (orient : FlipNode → FlipNode → Prop)
    (X Y Z : FlipNode) : Prop :=
  (X = T.node base 1 ∧ IsLeaf A Y.1 ∧
    IsLeaf A Z.1 ∧ orient Y Z) ∨
  (X = T.node base 2 ∧ IsLeaf A Y.1 ∧
    IsLeaf A Z.1 ∧ ¬ orient Y Z)

/-- The actual induced-preserving cross-branch marker extension. -/
def withCrossMarkerEdges
    (T : FlipFamily A ι) (base : ι)
    (orient : FlipNode → FlipNode → Prop) :
    Ordered3Graph FlipNode :=
  T.withCrossBranchEdges (T.crossMarkerExtra base orient)

/-- Already verified branch copies remain induced even after
all newly assigned cross-branch marker edges. -/
theorem withCrossMarkerEdges_induced
    (T : FlipFamily A ι) (base : ι)
    (orient : FlipNode → FlipNode → Prop)
    (i : ι) (x y z : Nat) (hxy : x < y) (hyz : y < z) :
    (T.withCrossMarkerEdges base orient).edge
      (T.node i x) (T.node i y) (T.node i z) ↔
      (T.graph i).edge x y z :=
  T.withCrossBranchEdges_induced (T.crossMarkerExtra base orient)
    i x y z hxy hyz

/-- For a cross-branch pair of leaves, marker 1 is present
exactly when the chosen orientation points to the right. -/
theorem cross_marker_one_iff
    (T : FlipFamily A ι) (base : ι)
    (orient : FlipNode → FlipNode → Prop)
    (Y Z : FlipNode)
    (hpair : T.OffBranchLeafPair Y Z) :
    (T.withCrossMarkerEdges base orient).edge
      (T.node base 1) Y Z ↔ orient Y Z := by
  rcases hpair with ⟨hY, hZ, hYZ, hNo⟩
  have hOld := T.no_shared_pair_no_raw_edge Y Z (T.node base 1) hNo
  have hOutside := T.no_shared_pair_no_span Y Z (T.node base 1) hNo
  have hMark : (T.node base 1).1 < Y.1 := by
    rw [T.node_level]
    have hLevel : 3 ≤ Y.1 := hY.1
    omega
  have hNe : T.node base 1 ≠ T.node base 2 := by
    intro h
    have hv := congrArg Prod.fst h
    simp only [node] at hv
    omega
  simp [withCrossMarkerEdges, withCrossBranchEdges,
    crossMarkerExtra, hOld, hOutside, hMark, hYZ, hY, hZ, hNe]

/-- Marker 2 is present exactly for the opposite choice. -/
theorem cross_marker_two_iff
    (T : FlipFamily A ι) (base : ι)
    (orient : FlipNode → FlipNode → Prop)
    (Y Z : FlipNode)
    (hpair : T.OffBranchLeafPair Y Z) :
    (T.withCrossMarkerEdges base orient).edge
      (T.node base 2) Y Z ↔ ¬ orient Y Z := by
  rcases hpair with ⟨hY, hZ, hYZ, hNo⟩
  have hOld := T.no_shared_pair_no_raw_edge Y Z (T.node base 2) hNo
  have hOutside := T.no_shared_pair_no_span Y Z (T.node base 2) hNo
  have hMark : (T.node base 2).1 < Y.1 := by
    rw [T.node_level]
    have hLevel : 3 ≤ Y.1 := hY.1
    omega
  have hNe : T.node base 2 ≠ T.node base 1 := by
    intro h
    have hv := congrArg Prod.fst h
    simp only [node] at hv
    omega
  simp [withCrossMarkerEdges, withCrossBranchEdges,
    crossMarkerExtra, hOld, hOutside, hMark, hYZ, hY, hZ, hNe]

/-- Exactly one marker is present at every off-branch leaf pair.
This is only the pairwise XOR part of the V3 axiom. -/
theorem cross_marker_exactly_one
    (T : FlipFamily A ι) (base : ι)
    (orient : FlipNode → FlipNode → Prop)
    (Y Z : FlipNode)
    (hpair : T.OffBranchLeafPair Y Z) :
    ((T.withCrossMarkerEdges base orient).edge
      (T.node base 1) Y Z ∧
     ¬ (T.withCrossMarkerEdges base orient).edge
      (T.node base 2) Y Z) ∨
    ((T.withCrossMarkerEdges base orient).edge
      (T.node base 2) Y Z ∧
     ¬ (T.withCrossMarkerEdges base orient).edge
      (T.node base 1) Y Z) := by
  classical
  have hOne := T.cross_marker_one_iff base orient Y Z hpair
  have hTwo := T.cross_marker_two_iff base orient Y Z hpair
  by_cases h : orient Y Z
  · exact Or.inl ⟨hOne.mpr h, fun hmark => (hTwo.mp hmark) h⟩
  · exact Or.inr ⟨hTwo.mpr h, fun hmark => h (hOne.mp hmark)⟩

end FlipFamily
end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
