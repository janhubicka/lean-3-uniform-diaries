import ThreeUniformDiaries.DiaryFiniteOrderedSumRightMarkerTypes

/-!
# E-only dichotomy for singleton meets involving genuine split vertices

In any ordered ternary relation whose edges obey the permitted
diary E1--E5 shapes, genuine split vertices have no incoming
singleton tests with middle coordinate at or above 3. Further,
a leaf and a split differ already in the marker 0,1,2 profile.

Consequently, if two nonmarker vertices include a genuine split,
their singleton meet is either already BELOW marker cut 3, or is
exactly capped at their smaller coordinate. There cannot be a
genuine proper first disagreement at a later nonmarker vertex.

This is a useful proof-reduction for transporting *mixed* meets
under finite leaf preembeddings after target flips: exact leaf
meets may need special protection, but split-involving singleton
meets reduce to marker bits and the numeric minimum.

No S1/S2, V1/V2/V3, global prediary or embedding is assumed here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- If one endpoint is a genuine split, then either a marker
test distinguishes the two endpoints before level three, or
their entire singleton types agree until the capped endpoint. -/
theorem E_split_oneMeet_small_or_capped
    (hE : ∀ x y z : Nat, H.edge x y z →
      PermittedDiaryEdge H x y z)
    (u v : Nat) (hu3 : 3 ≤ u) (hv3 : 3 ≤ v)
    (huRole : IsLeaf H u ∨ IsDiarySplit H u)
    (hvRole : IsLeaf H v ∨ IsDiarySplit H v)
    (hSplit : IsDiarySplit H u ∨ IsDiarySplit H v) :
    H.oneMeetLevel u v < 3 ∨
      H.oneMeetLevel u v = min u v := by
  classical
  by_cases hMarker : H.SameOneTypeBelow 3 u v
  · have hBoth : IsDiarySplit H u ∧ IsDiarySplit H v := by
      rcases hSplit with huSplit | hvSplit
      · rcases hvRole with hvLeaf | hvSplit
        · exact False.elim
            ((split_leaf_not_sameOneType_three H u v
              huSplit hvLeaf) hMarker)
        · exact ⟨huSplit,hvSplit⟩
      · rcases huRole with huLeaf | huSplit
        · exact False.elim
            ((leaf_split_not_sameOneType_three H u v
              huLeaf hvSplit) hMarker)
        · exact ⟨huSplit,hvSplit⟩
    have hMin3 : 3 ≤ min u v := by omega
    have hAtCap : H.SameOneTypeBelow (min u v) u v :=
      (E_split_oneType_stable hE (min u v) u v
        hMin3 hBoth.1 hBoth.2).mpr hMarker
    have hLower : min u v ≤ H.oneMeetLevel u v :=
      Nat.le_findGreatest (le_refl _) hAtCap
    exact Or.inr
      (le_antisymm (H.oneMeetLevel_le_min u v) hLower)
  · have hSmall : H.oneMeetLevel u v < 3 := by
      by_contra hBad
      have hGe : 3 ≤ H.oneMeetLevel u v := by omega
      have hAgree : H.SameOneTypeBelow 3 u v := by
        intro a b hab hb
        exact (H.oneMeetLevel_agree u v) hab (by omega)
      exact hMarker hAgree
    exact Or.inl hSmall

end DiaryLeafPriority
end ThreeUniformDiaries
