import ThreeUniformDiaries.DiaryOnePassSourceLeafMarkerBase
import ThreeUniformDiaries.DiaryPrediaryRoleNextCut

/-!
# Every original singleton meet of source leaves is a leaf or a 1-split

A two-split is forbidden as the middle coordinate of every permitted
increasing edge, so passing a two-split introduces NO new singleton
test. It therefore cannot be the first proper singleton disagreement
of two vertices.

A capped singleton meet of two source leaves is one of the leaves
and is itself a leaf. The initial marker-prefix lemma supplies the
lower bound m>=3 needed to apply the source pre-diary role partition.
Together these observations show that the literal first singleton
meet of two source leaves has only the two cases needed by global
one-pass LexEarlier preservation: old 1-split or old leaf.

No source S1/S2 or target diary is used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- An original two-split can never be the proper first singleton
type disagreement of any two vertices (not just leaves). -/
theorem onePass_source_twoSplit_not_proper_oneMeet
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsTwoSplit H m)
    (hmu : m < u) (hmv : m < v)
    (hMeet : H.oneMeetLevel u v = m) : False := by
  classical
  have hBefore : H.SameOneTypeBelow m u v := by
    rw [← hMeet]
    exact H.oneMeetLevel_agree u v
  have hNext : H.SameOneTypeBelow (m + 1) u v := by
    apply (H.sameOneTypeBelow_succ_iff m u v).mpr
    refine ⟨hBefore, ?_⟩
    intro a ha
    exact iff_of_false
      (P.twoSplit_no_middle m a u hm)
      (P.twoSplit_no_middle m a v hm)
  have hBound : m + 1 ≤ min u v := by omega
  have hTooFar : m + 1 ≤ H.oneMeetLevel u v :=
    Nat.le_findGreatest hBound hNext
  rw [hMeet] at hTooFar
  omega

/-- For two actual source leaves, the first singleton meet is
either a genuine source leaf or a genuine source 1-split.
The discarded source 2-split case would require a forbidden
middle-coordinate test. This is V/E-only, not S1. -/
theorem onePass_source_leafOneMeet_is_leaf_or_oneSplit
    (P : RolePrediary H) (u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v) :
    IsLeaf H (H.oneMeetLevel u v) ∨
      IsOneSplit H (H.oneMeetLevel u v) := by
  classical
  let m := H.oneMeetLevel u v
  have hm3 : 3 ≤ m :=
    onePass_source_leaf_oneMeet_ge_three P u v hu hv
  have hBound : m ≤ min u v := H.oneMeetLevel_le_min u v
  rcases P.role_valid m hm3 with hLeaf | hOne | hTwo
  · exact Or.inl hLeaf
  · exact Or.inr hOne
  · by_cases hCap : m = min u v
    · have hmLeaf : IsLeaf H m := by
        rcases le_total u v with huv | hvu
        · have hmU : m = u := by
            rw [hCap, min_eq_left huv]
          simpa only [hmU] using hu
        · have hmV : m = v := by
            rw [hCap, min_eq_right hvu]
          simpa only [hmV] using hv
      exact False.elim (hmLeaf.2.2 hTwo.2.2)
    · have hmu : m < u := by omega
      have hmv : m < v := by omega
      exact False.elim
        (onePass_source_twoSplit_not_proper_oneMeet
          P m u v hTwo hmu hmv rfl)

end DiaryLeafPriority
end ThreeUniformDiaries
