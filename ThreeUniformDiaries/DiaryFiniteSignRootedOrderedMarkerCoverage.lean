import ThreeUniformDiaries.DiaryFiniteSignRootedCrossMarkerExtension

/-!
# Marker coverage for tied source levels after ordering raw nodes

Distinct sign-rooted raw nodes can have the SAME original source level.
Once a final total order is chosen, two such leaf nodes need a Devlin
marker edge. The first extension only treated strictly increasing
source levels, hence did not cover these ties.

This variant accepts an explicit proposed order relation on raw nodes
and allows equal original source levels. It preserves ALL original
flip branches inducedly and makes exactly one marker incident with
every ordered off-branch leaf pair.

The relation need not yet satisfy linearity or the literal V3
lexicographic rule. Cross-branch positive V1/V2 coherence remains
to be checked after markers are inserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- An ordered off-branch pair, including possible ties of
original source levels. The ambient order is supplied explicitly. -/
structure OrderedOffBranchLeafPair
    (F : FiniteSignRootedFlipFamily A n ι)
    (before : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (Y Z : FiniteSignRootedNode A n) : Prop where
  leafY : IsLeaf A Y.1
  leafZ : IsLeaf A Z.1
  ordered : before Y Z
  separated : ¬ F.SharedBranchPair Y Z

/-- Two raw nodes at the same source level cannot occur as
an increasing ordered pair within a single original branch. -/
theorem sameLevel_no_shared_branch_pair
    (F : FiniteSignRootedFlipFamily A n ι)
    (Y Z : FiniteSignRootedNode A n)
    (hLevel : Y.1 = Z.1) :
    ¬ F.SharedBranchPair Y Z := by
  rintro ⟨i,y,z,hyz,hzn,hY,hZ⟩
  have hy : y = Y.1 := by
    have h := congrArg Prod.fst hY
    simpa only [F.node_level] using h
  have hz : z = Z.1 := by
    have h := congrArg Prod.fst hZ
    simpa only [F.node_level] using h
  omega

/-- No old raw hyperedge can end in two nodes of equal
original source level, regardless of its first vertex. -/
theorem sameLevel_no_raw_terminal_pair_edge
    (F : FiniteSignRootedFlipFamily A n ι)
    (X Y Z : FiniteSignRootedNode A n)
    (hLevel : Y.1 = Z.1) :
    ¬ (F.rawAmalgam).edge X Y Z := by
  intro h
  exact (F.sameLevel_no_shared_branch_pair Y Z hLevel)
    (F.raw_edge_implies_shared_branch_pair X Y Z h)

/-- Candidate extension under any explicit proposed ambient order. -/
def withOrderedCrossMarkerEdges
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop) :
    Ordered3Graph (FiniteSignRootedNode A n) where
  edge X Y Z :=
    (F.rawAmalgam).edge X Y Z ∨
    (X = F.node base 1 ∧
      F.OrderedOffBranchLeafPair before Y Z ∧ orient Y Z) ∨
    (X = F.node base 2 ∧
      F.OrderedOffBranchLeafPair before Y Z ∧ ¬ orient Y Z)

/-- Every original source flip remains induced, including nonedges
and the original two Devlin marker columns. -/
theorem withOrderedCrossMarkerEdges_induced
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (i : ι) (x y z : Nat)
    (hxy : x < y) (hyz : y < z) (hzn : z < n) :
    (F.withOrderedCrossMarkerEdges base before orient).edge
      (F.node i x) (F.node i y) (F.node i z) ↔
      (F.graph i).edge x y z := by
  have hShared : F.SharedBranchPair (F.node i y)
      (F.node i z) := ⟨i,y,z,hyz,hzn,rfl,rfl⟩
  constructor
  · intro h
    rcases h with hOld | ⟨_,hOff,_⟩ | ⟨_,hOff,_⟩
    · exact (F.rawAmalgam_edge_iff i x y z hxy hyz hzn).mp hOld
    · exact False.elim (hOff.separated hShared)
    · exact False.elim (hOff.separated hShared)
  · intro h
    exact Or.inl
      ((F.rawAmalgam_edge_iff i x y z hxy hyz hzn).mpr h)

/-- Marker one equals the chosen orientation on every newly
ordered off-branch leaf pair, including equal-level pairs. -/
theorem ordered_cross_marker_one_iff
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (Y Z : FiniteSignRootedNode A n)
    (hOff : F.OrderedOffBranchLeafPair before Y Z) :
    (F.withOrderedCrossMarkerEdges base before orient).edge
      (F.node base 1) Y Z ↔ orient Y Z := by
  have hNoRaw :
      ¬ (F.rawAmalgam).edge (F.node base 1) Y Z := by
    intro h
    exact hOff.separated
      (F.raw_edge_implies_shared_branch_pair _ _ _ h)
  have hNe : F.node base 1 ≠ F.node base 2 := by
    intro h
    have hh := congrArg Prod.fst h
    simp only [F.node_level] at hh
    omega
  constructor
  · intro h
    rcases h with hOld | ⟨_,_,hOrient⟩ | ⟨hMark,_,_⟩
    · exact False.elim (hNoRaw hOld)
    · exact hOrient
    · exact False.elim (hNe hMark)
  · intro h
    exact Or.inr (Or.inl ⟨rfl,hOff,h⟩)

/-- Marker two is the complement of the same orientation. -/
theorem ordered_cross_marker_two_iff
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (Y Z : FiniteSignRootedNode A n)
    (hOff : F.OrderedOffBranchLeafPair before Y Z) :
    (F.withOrderedCrossMarkerEdges base before orient).edge
      (F.node base 2) Y Z ↔ ¬ orient Y Z := by
  have hNoRaw :
      ¬ (F.rawAmalgam).edge (F.node base 2) Y Z := by
    intro h
    exact hOff.separated
      (F.raw_edge_implies_shared_branch_pair _ _ _ h)
  have hNe : F.node base 2 ≠ F.node base 1 := by
    intro h
    have hh := congrArg Prod.fst h
    simp only [F.node_level] at hh
    omega
  constructor
  · intro h
    rcases h with hOld | ⟨hMark,_,_⟩ | ⟨_,_,hOrient⟩
    · exact False.elim (hNoRaw hOld)
    · exact False.elim (hNe hMark)
    · exact hOrient
  · intro h
    exact Or.inr (Or.inr ⟨rfl,hOff,h⟩)

/-- XOR marker coverage holds also for same-source-level leaves. -/
theorem ordered_cross_marker_exactly_one
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (Y Z : FiniteSignRootedNode A n)
    (hOff : F.OrderedOffBranchLeafPair before Y Z) :
    ((F.withOrderedCrossMarkerEdges base before orient).edge
      (F.node base 1) Y Z ∧
     ¬ (F.withOrderedCrossMarkerEdges base before orient).edge
       (F.node base 2) Y Z) ∨
    ((F.withOrderedCrossMarkerEdges base before orient).edge
      (F.node base 2) Y Z ∧
     ¬ (F.withOrderedCrossMarkerEdges base before orient).edge
       (F.node base 1) Y Z) := by
  classical
  have hOne := F.ordered_cross_marker_one_iff
    base before orient Y Z hOff
  have hTwo := F.ordered_cross_marker_two_iff
    base before orient Y Z hOff
  by_cases h : orient Y Z
  · exact Or.inl
      ⟨hOne.mpr h, fun he => (hTwo.mp he) h⟩
  · exact Or.inr
      ⟨hTwo.mpr h, fun he => h (hOne.mp he)⟩

/-- The newly permitted same-source-level case now receives a
marker whenever the proposed ambient order compares the leaves. -/
theorem sameLevel_ordered_leaf_pair_gets_marker
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (Y Z : FiniteSignRootedNode A n)
    (hLevel : Y.1 = Z.1)
    (hY : IsLeaf A Y.1) (hZ : IsLeaf A Z.1)
    (hBefore : before Y Z) :
    ((F.withOrderedCrossMarkerEdges base before orient).edge
      (F.node base 1) Y Z ∧
     ¬ (F.withOrderedCrossMarkerEdges base before orient).edge
       (F.node base 2) Y Z) ∨
    ((F.withOrderedCrossMarkerEdges base before orient).edge
      (F.node base 2) Y Z ∧
     ¬ (F.withOrderedCrossMarkerEdges base before orient).edge
       (F.node base 1) Y Z) := by
  apply F.ordered_cross_marker_exactly_one
    base before orient Y Z
  exact ⟨hY,hZ,hBefore,
    F.sameLevel_no_shared_branch_pair Y Z hLevel⟩

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
