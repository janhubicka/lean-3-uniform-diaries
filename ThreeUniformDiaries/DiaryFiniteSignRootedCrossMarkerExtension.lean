import ThreeUniformDiaries.DiaryFiniteCanonicalSignRootedCarrier
import ThreeUniformDiaries.DiaryFiniteSignRootedRawTerminalSupport

/-!
# An induced-preserving cross-branch marker extension of the sign-rooted tree

The raw sign-rooted flip tree is an actual finite relational
amalgam, but incomparable leaves have neither of the two
required Devlin marker edges. This module adds those missing
cross-branch edges, one for marker 1 or marker 2, according to
a freely supplied orientation predicate on off-branch leaf pairs.

The edge extension is guarded by the absence of any ORIGINAL
source branch containing both leaf nodes. Thus every genuine
source flip branch remains an INDUCED relational copy, including
all original nonedges; marker levels 0,1,2 remain shared.

For each off-branch ordered leaf pair exactly one of the two
cross-marker incidences is present. This verifies ONLY the
exclusive-or/coverage part of V3. An arbitrary orientation
may disagree with the literal LexEarlier relation determined
by the enlarged one-type tree. Furthermore, new cross-marker
edges can alter predecessor singleton types, so the raw
V1/V2 theorems DO NOT automatically transfer to this extension.

The next geometric obligation is to choose the orientation
coherently enough to satisfy the exact V3 comparison AND
preserve all positive parent V1/V2 types at shared splits.
No complete pre-diary or general absorber is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- Two raw nodes are realised on the SAME genuine flip branch
as an increasing pair of actual bounded source vertices. -/
def SharedBranchPair (F : FiniteSignRootedFlipFamily A n ι)
    (Y Z : FiniteSignRootedNode A n) : Prop :=
  ∃ (i : ι) (y z : Nat),
    y < z ∧ z < n ∧
    F.node i y = Y ∧ F.node i z = Z

/-- Genuine source leaves on different sign-rooted branches,
which NEVER occur together in any original flip copy. -/
structure OffBranchLeafPair
    (F : FiniteSignRootedFlipFamily A n ι)
    (Y Z : FiniteSignRootedNode A n) : Prop where
  leafY : IsLeaf A Y.1
  leafZ : IsLeaf A Z.1
  order : Y.1 < Z.1
  separated : ¬ F.SharedBranchPair Y Z

/-- Every RAW edge is contained in one actual branch and hence
its final two nodes are a shared-branch pair. -/
theorem raw_edge_implies_shared_branch_pair
    (F : FiniteSignRootedFlipFamily A n ι)
    (X Y Z : FiniteSignRootedNode A n)
    (h : (F.rawAmalgam).edge X Y Z) :
    F.SharedBranchPair Y Z := by
  obtain ⟨i,x,y,z,hxy,hyz,hzn,hX,hY,hZ,hEdge⟩ := h
  exact ⟨i,y,z,hyz,hzn,hY,hZ⟩

/-- The actual sign-rooted graph after adding cross-marker
incidences for off-branch ordered leaf pairs only. The
orientation is an arbitrary Prop-valued predicate: it is
not yet asserted to coincide with the literal V3 lex order. -/
def withCrossMarkerEdges
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop) :
    Ordered3Graph (FiniteSignRootedNode A n) where
  edge X Y Z :=
    (F.rawAmalgam).edge X Y Z ∨
    (X = F.node base 1 ∧ F.OffBranchLeafPair Y Z ∧
      orient Y Z) ∨
    (X = F.node base 2 ∧ F.OffBranchLeafPair Y Z ∧
      ¬ orient Y Z)

/-- Every genuine source flip is still an induced branch,
including its original marker incidences and all nonedges.
The new cross-marker edges are absent on every original
source branch pair, irrespective of the orientation function. -/
theorem withCrossMarkerEdges_induced
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (i : ι) (x y z : Nat)
    (hxy : x < y) (hyz : y < z) (hzn : z < n) :
    (F.withCrossMarkerEdges base orient).edge
      (F.node i x) (F.node i y) (F.node i z) ↔
      (F.graph i).edge x y z := by
  have hPair :
      F.SharedBranchPair (F.node i y) (F.node i z) :=
    ⟨i,y,z,hyz,hzn,rfl,rfl⟩
  constructor
  · intro h
    rcases h with hOld | ⟨hMark,hOff,hOrient⟩ |
        ⟨hMark,hOff,hOrient⟩
    · exact (F.rawAmalgam_edge_iff i x y z hxy hyz hzn).mp hOld
    · exact False.elim (hOff.separated hPair)
    · exact False.elim (hOff.separated hPair)
  · intro h
    exact Or.inl
      ((F.rawAmalgam_edge_iff i x y z hxy hyz hzn).mpr h)

/-- The marker-1 incidence of any OFF-BRANCH ordered leaf pair
is exactly the chosen orientation. No old raw marker edge can
conflict with that choice. -/
theorem cross_marker_one_iff
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (Y Z : FiniteSignRootedNode A n)
    (hOff : F.OffBranchLeafPair Y Z) :
    (F.withCrossMarkerEdges base orient).edge
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
    rcases h with hOld | ⟨hMark,hOff',hOrient⟩ |
        ⟨hMark,hOff',hOrient⟩
    · exact False.elim (hNoRaw hOld)
    · exact hOrient
    · exact False.elim (hNe hMark)
  · intro h
    exact Or.inr (Or.inl ⟨rfl,hOff,h⟩)

/-- The marker-2 incidence is the complement of the SAME
chosen orientation at every off-branch ordered leaf pair. -/
theorem cross_marker_two_iff
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (Y Z : FiniteSignRootedNode A n)
    (hOff : F.OffBranchLeafPair Y Z) :
    (F.withCrossMarkerEdges base orient).edge
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
    rcases h with hOld | ⟨hMark,hOff',hOrient⟩ |
        ⟨hMark,hOff',hOrient⟩
    · exact False.elim (hNoRaw hOld)
    · exact False.elim (hNe hMark)
    · exact hOrient
  · intro h
    exact Or.inr (Or.inr ⟨rfl,hOff,h⟩)

/-- Exactly one cross-branch Devlin marker edge is present,
while every original genuine flip branch stays induced.
This XOR clause is NOT the full V3 lexicographic axiom. -/
theorem cross_marker_exactly_one
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (Y Z : FiniteSignRootedNode A n)
    (hOff : F.OffBranchLeafPair Y Z) :
    ((F.withCrossMarkerEdges base orient).edge
      (F.node base 1) Y Z ∧
     ¬ (F.withCrossMarkerEdges base orient).edge
      (F.node base 2) Y Z) ∨
    ((F.withCrossMarkerEdges base orient).edge
      (F.node base 2) Y Z ∧
     ¬ (F.withCrossMarkerEdges base orient).edge
      (F.node base 1) Y Z) := by
  classical
  have hOne := F.cross_marker_one_iff base orient Y Z hOff
  have hTwo := F.cross_marker_two_iff base orient Y Z hOff
  by_cases h : orient Y Z
  · exact Or.inl
      ⟨hOne.mpr h, fun he => (hTwo.mp he) h⟩
  · exact Or.inr
      ⟨hTwo.mpr h, fun he => h (hOne.mp he)⟩

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
