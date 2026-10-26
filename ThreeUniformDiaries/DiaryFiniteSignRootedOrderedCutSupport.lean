import ThreeUniformDiaries.DiaryFiniteSignRootedOrderedMarkerCoverage
import ThreeUniformDiaries.DiaryFiniteSignRootedRawTerminalSupport

/-!
# Original-level support of marker-extended edges at finite split cuts

The ordered marker extension has two edge sources: increasing
triples from original source branches, and new Devlin marker
triples. In BOTH cases the original level of the first vertex
is strictly less than the original level of the second.
This holds EVEN when the last two leaves are tied at their
original source level and ordered only by a later tie-break.

Consequently any predecessor test with first original source
level >= the second is always false. Moreover at a genuine
source split s, an earlier raw node X of original level s,
different from the branch's split node at s, cannot occur as
the FIRST vertex of a nonzero auxiliary pair test whose two
terminal vertices lie on that source branch: terminal locality
excludes raw edges and X cannot be a Devlin marker.

These facts complement the same-level MIDDLE-vertex zero
lemma in PR #890 and are needed for passing from source-level
prefix tests to the actual rank cut of a totally enumerated
finite sign-rooted node carrier.

No genuine V3 comparison or general finite diary absorber
is asserted in this module.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- The first two raw nodes of EVERY marker-extended edge
have strictly increasing ORIGINAL source levels.
Only the last two levels may tie in the new extension. -/
theorem orderedMarker_edge_first_level_lt_second
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (X Y Z : FiniteSignRootedNode A n)
    (h : (F.withOrderedCrossMarkerEdges base before orient).edge
      X Y Z) :
    X.1 < Y.1 := by
  rcases h with hRaw | ⟨hMark,hOff,_⟩ |
      ⟨hMark,hOff,_⟩
  · obtain ⟨i,x,y,z,hxy,hyz,hzn,hX,hY,hZ,he⟩ := hRaw
    have hXlevel : X.1 = x := by
      have hh := congrArg Prod.fst hX
      simpa only [F.node_level] using hh.symm
    have hYlevel : Y.1 = y := by
      have hh := congrArg Prod.fst hY
      simpa only [F.node_level] using hh.symm
    omega
  · have hXlevel : X.1 = 1 := by
      rw [hMark]
      exact F.node_level base 1
    have hYlevel : 3 ≤ Y.1 := hOff.leafY.1
    omega
  · have hXlevel : X.1 = 2 := by
      rw [hMark]
      exact F.node_level base 2
    have hYlevel : 3 ≤ Y.1 := hOff.leafY.1
    omega

/-- An earlier raw node X tied to a genuine source split
level s, but different from that branch's split node,
cannot occur as the FIRST vertex of ANY ordered marker-
extended edge ending in two vertices on the same branch.
No orientation assumption is needed. -/
theorem orderedMarker_sameLevel_offpath_aux_test_false
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (i : ι) (s u v : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (X : FiniteSignRootedNode A n)
    (hLevel : X.1 = s)
    (hDifferent : X ≠ F.node i s) :
    ¬ (F.withOrderedCrossMarkerEdges base before orient).edge
      X (F.node i u) (F.node i v) := by
  have hs3 : 3 ≤ s := by
    rcases hs with hOne | hTwo
    · exact hOne.1
    · exact hTwo.1
  intro h
  rcases h with hRaw | ⟨hMark,_,_⟩ |
      ⟨hMark,_,_⟩
  · have hXprefix :=
      (F.rawAmalgam_edge_last_prefix_nodes
        i X (F.node i u) v hRaw).1
    have hEq : X = F.node i s := by
      simpa only [hLevel] using hXprefix
    exact hDifferent hEq
  · have hx : X.1 = 1 := by
      rw [hMark]
      exact F.node_level base 1
    omega
  · have hx : X.1 = 2 := by
      rw [hMark]
      exact F.node_level base 2
    omega

/-- Different branches with a shared split node also agree
on ALL additional same-level first-coordinate auxiliary
predecessor tests: both sides are FALSE. -/
theorem orderedMarker_sharedSplit_sameLevel_aux_tests_agree
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (i j : ι) (s u v w z : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (hShared : F.node i s = F.node j s)
    (X : FiniteSignRootedNode A n)
    (hLevel : X.1 = s)
    (hDifferent : X ≠ F.node i s) :
    (F.withOrderedCrossMarkerEdges base before orient).edge
        X (F.node i u) (F.node i v) ↔
      (F.withOrderedCrossMarkerEdges base before orient).edge
        X (F.node j w) (F.node j z) := by
  have hDifferentJ : X ≠ F.node j s := by
    intro h
    exact hDifferent (h.trans hShared.symm)
  exact iff_of_false
    (F.orderedMarker_sameLevel_offpath_aux_test_false
      base before orient i s u v hs X hLevel hDifferent)
    (F.orderedMarker_sameLevel_offpath_aux_test_false
      base before orient j s w z hs X hLevel hDifferentJ)

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
