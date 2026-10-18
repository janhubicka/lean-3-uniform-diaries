import ThreeUniformDiaries.DiaryProtectedMixedFullMeets
import ThreeUniformDiaries.DiaryOnePassTargetS2Cap
import ThreeUniformDiaries.DiaryOnePassTargetS2MarkerDichotomy

/-!
# Relative one-pass preservation of protected leaf-pair meets

In an ambient V/E pre-diary a completed protected diary may have
pairs of original leaves whose full two-type meet is:
* the marker 1;
* a genuine ORIGINAL 2-split; or
* the common first leaf of the two ordered pairs.

The old-split and marker cases are already covered by the local
one-pass theorems. At a common-first-leaf cap, the protected S1
condition on the two second coordinates forces agreement through
the next original source cut. Thus no fresh pair event separates
the capped pairs.

All claims concern literal source/target numerical meet levels.
The strong (false) preservation of ALL old type agreements at
old-leaf image cuts is not assumed or concluded.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- At a common first leaf a, a pair-type cap really passes through
the next original source cut if the two second leaves coincide or
meet at an old genuine 1-split. This is the missing finite protected
S2-cap input to the checked one-pass cap transport theorem. -/
theorem RolePrediary.protected_common_first_nextTwoType
    (P : RolePrediary H) (a b d : Nat)
    (ha : IsLeaf H a)
    (hab : a < b) (had : a < d)
    (hMeet : H.twoMeetLevel a b a d = a)
    (hBD : b = d ∨ IsOneSplit H (H.oneMeetLevel b d)) :
    H.SameTwoTypeBelow (a + 1) a b a d := by
  classical
  have hAtA : H.SameTwoTypeBelow a a b a d := by
    simpa only [hMeet] using (H.twoMeetLevel_agree a b a d)
  have hSecond : H.SameOneTypeBelow (a + 1) b d := by
    rcases hBD with hEq | hOne
    · subst d
      intro x y hxy hy
      rfl
    · have hLower : a ≤ H.oneMeetLevel b d :=
        Nat.le_findGreatest (by omega : a ≤ min b d) hAtA.2.1
      have hDifferent : H.oneMeetLevel b d ≠ a := by
        intro heq
        have hOneAtA : IsOneSplit H a := by
          simpa only [heq] using hOne
        exact ha.2.1 hOneAtA.2.1
      have hPast : a + 1 ≤ H.oneMeetLevel b d := by omega
      intro x y hxy hy
      exact (H.oneMeetLevel_agree b d) hxy (by omega)
  refine ⟨?_, hSecond, ?_⟩
  · intro x y hxy hy
    rfl
  · intro x hx
    by_cases hxa : x < a
    · exact hAtA.2.2 hxa
    · have hEq : x = a := by omega
      subst x
      have hNotAB : ¬ H.edge a a b := by
        intro he
        have ho := P.edge_ordered a a b he
        omega
      have hNotAD : ¬ H.edge a a d := by
        intro he
        have ho := P.edge_ordered a a d he
        omega
      exact iff_of_false hNotAB hNotAD

/-- For two ordered pairs of old leaves, preservation of the
complete leaf-pair numerical meet follows whenever the source
meet is marker 1, an old 2-split, or a *common-first-leaf* cap.
The last case needs only protected S1 for the second coordinates.
This is the leaf-only complement to #648's mixed-pair theorem. -/
theorem onePass_protected_leaf_twoMeet_preserved
    (P : RolePrediary H) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hSourceCase :
      H.twoMeetLevel a b c d = 1 ∨
      IsTwoSplit H (H.twoMeetLevel a b c d) ∨
      (a = c ∧ H.twoMeetLevel a b c d = a))
    (hBD : b = d ∨ IsOneSplit H (H.oneMeetLevel b d)) :
    (onePassRawTarget H).twoMeetLevel
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) =
      onePassOldImage H (H.twoMeetLevel a b c d) := by
  classical
  let G := onePassRawTarget H
  let f := onePassOldImage H
  rcases hSourceCase with hOne | hTwo | ⟨hAC, hCap⟩
  · have hSourceDifferent :
        ¬ (H.edge 1 a b ↔ H.edge 1 c d) := by
      intro hSame
      have hAgree := P.sameMarkerOne_twoTypeBelow_three
        a b c d hab hcd ha hb hc hd hSame
      have hCapBound : 3 ≤ min a c := by
        have ha3 := ha.1
        have hc3 := hc.1
        omega
      have hGe : 3 ≤ H.twoMeetLevel a b c d :=
        Nat.le_findGreatest hCapBound hAgree
      rw [hOne] at hGe
      omega
    have hAB :
        G.edge 1 (f a) (f b) ↔ H.edge 1 a b := by
      simpa only [onePassOldImage_one] using
        (onePassRawTarget_edge_image_iff H 1 a b)
    have hCD :
        G.edge 1 (f c) (f d) ↔ H.edge 1 c d := by
      simpa only [onePassOldImage_one] using
        (onePassRawTarget_edge_image_iff H 1 c d)
    have hTargetDifferent :
        ¬ (G.edge 1 (f a) (f b) ↔ G.edge 1 (f c) (f d)) := by
      intro h
      exact hSourceDifferent (hAB.symm.trans (h.trans hCD))
    have hTargetOne : G.twoMeetLevel (f a) (f b) (f c) (f d) = 1 :=
      onePassRawTarget_twoMeet_eq_one_of_marker_disagreement P
        (f a) (f b) (f c) (f d)
        ((onePassRawTarget_old_leaf_iff H a).mpr ha)
        ((onePassRawTarget_old_leaf_iff H c).mpr hc)
        hTargetDifferent
    calc
      G.twoMeetLevel (f a) (f b) (f c) (f d) = 1 := hTargetOne
      _ = f (H.twoMeetLevel a b c d) := by
        rw [hOne]
        exact (onePassOldImage_one H).symm
  · let m := H.twoMeetLevel a b c d
    have hBound := H.twoMeetLevel_le_min a b c d
    have hma : m < a := by
      have hle : m ≤ a := hBound.trans (min_le_left _ _)
      have hne : m ≠ a := by
        intro hEq
        have ht : IsTwoSplit H a := by
          change IsTwoSplit H m at hTwo
          simpa only [hEq] using hTwo
        exact ha.2.2 ht.2.2
      omega
    have hmc : m < c := by
      have hle : m ≤ c := hBound.trans (min_le_right _ _)
      have hne : m ≠ c := by
        intro hEq
        have ht : IsTwoSplit H c := by
          change IsTwoSplit H m at hTwo
          simpa only [hEq] using hTwo
        exact hc.2.2 ht.2.2
      omega
    exact onePass_oldTwoSplit_meet_exact P m a b c d
      hTwo hab hcd ha hb hc hd hma hmc rfl
  · subst c
    have hNext : H.SameTwoTypeBelow (a + 1) a b a d :=
      P.protected_common_first_nextTwoType
        a b d ha hab hcd hCap hBD
    have hTargetCap :=
      onePass_source_leaf_cap_twoMeet_preserved
        P a a b a d ha ha hb ha hd
        hab hcd (le_refl _) (le_refl _) (by simp)
        hCap hNext
    rw [hCap]
    simpa only [min_self] using hTargetCap

end DiaryLeafPriority
end ThreeUniformDiaries
