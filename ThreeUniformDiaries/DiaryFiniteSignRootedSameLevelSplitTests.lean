import ThreeUniformDiaries.DiaryFiniteSignRootedOrderedMarkerCoverage
import ThreeUniformDiaries.DiaryFiniteSignRootedRawTerminalSupport

/-!
# Extra same-original-level predecessor tests at shared split cuts are zero

A final linearization of the sign-rooted finite carrier will
place different raw nodes with the SAME original source level
in some order. At a shared source split node S of original
level s, other nodes Y of the same level may therefore become
earlier vertices of the eventual enumerated pre-diary.

These tests are not covered by the existing raw predecessor
type comparisons, which quantify over source levels < s.
Fortunately, all raw nodes of original source level s have
the SAME source role. If s is a genuine one-/two-split,
then Y is NOT a source leaf, so no newly added Devlin marker
edge can use it as the middle vertex. If Y is not the chosen
branch's node at s, raw terminal locality makes ALL raw edges
with Y as middle vertex absent at later branch terminals.

Thus the extra same-source-level predecessor tests against
each positive descendant at the shared split are uniformly
FALSE, regardless of the candidate order and marker orientation.
This is a geometric input for translating the source-level V1/V2
stability lemmas into genuine rank-cut V1/V2 after linearly
enumerating the finite carrier.

No full V3, finite pre-diary or every-flip absorber is proved here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- A genuine source 1- or 2-split vertex is never a leaf,
in any finite diary graph (indeed the role definitions alone
already imply this). -/
theorem splitRole_not_leaf
    (A : Ordered3Graph Nat) (s : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s) :
    ¬ IsLeaf A s := by
  intro hLeaf
  rcases hs with hOne | hTwo
  · exact hLeaf.2.1 hOne.2.1
  · exact hLeaf.2.2 hTwo.2.2

/-- An earlier raw node Y of the SAME original source level
as a genuine source split s, but different from the branch's
split node at s, cannot participate in ANY marker-extended
ternary edge ending at a later node of that branch.

The conclusion holds under arbitrary ambient ordering and
arbitrary off-branch marker orientation; in particular it
covers ties after the ordered marker extension. -/
theorem orderedMarker_sameLevel_offpath_split_test_false
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (i : ι) (s u : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (hY : FiniteSignRootedNode A n)
    (hLevel : hY.1 = s)
    (hDifferent : hY ≠ F.node i s)
    (X : FiniteSignRootedNode A n) :
    ¬ (F.withOrderedCrossMarkerEdges base before orient).edge
      X hY (F.node i u) := by
  have hNoLeaf : ¬ IsLeaf A hY.1 := by
    rw [hLevel]
    exact splitRole_not_leaf A s hs
  intro h
  rcases h with hRaw | ⟨_,hOff,_⟩ | ⟨_,hOff,_⟩
  · have hYPrefix :=
      (F.rawAmalgam_edge_last_prefix_nodes i X hY u hRaw).2
    have hYSource : hY = F.node i s := by
      simpa only [hLevel] using hYPrefix
    exact hDifferent hYSource
  · exact hNoLeaf hOff.leafY
  · exact hNoLeaf hOff.leafY

/-- Two branches sharing their raw node at genuine split s
have IDENTICALLY FALSE tests at any other raw node Y of
original source level s, for all their later vertices.

This is precisely the same-level predecessor comparison
not supplied by the strict source-level-cut interface. -/
theorem orderedMarker_sharedSplit_sameLevel_tests_agree
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (i j : ι) (s u v : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (hShared : F.node i s = F.node j s)
    (Y : FiniteSignRootedNode A n)
    (hLevel : Y.1 = s)
    (hDifferent : Y ≠ F.node i s)
    (X : FiniteSignRootedNode A n) :
    (F.withOrderedCrossMarkerEdges base before orient).edge
        X Y (F.node i u) ↔
      (F.withOrderedCrossMarkerEdges base before orient).edge
        X Y (F.node j v) := by
  have hDifferentJ : Y ≠ F.node j s := by
    intro h
    exact hDifferent (h.trans hShared.symm)
  exact iff_of_false
    (F.orderedMarker_sameLevel_offpath_split_test_false
      base before orient i s u hs Y hLevel hDifferent X)
    (F.orderedMarker_sameLevel_offpath_split_test_false
      base before orient j s v hs Y hLevel hDifferentJ X)

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
