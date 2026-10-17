import ThreeUniformDiaries.DiaryOnePassPairSiblingTwoSplit
import ThreeUniformDiaries.DiaryOnePassTargetS2Cap
import ThreeUniformDiaries.DiaryOnePassTargetS2MarkerDichotomy
import ThreeUniformDiaries.DiaryOnePassOldSplitWitnessTransport
import ThreeUniformDiaries.DiaryOnePassTargetS1

/-!
# Complete S2 for the actual one-pass target; full diary completion

Let (u,v),(a,b) be ordered source leaf pairs, and put
m = twoMeetLevel_H(u,v,a,b). Source V/E and the two complementary
Devlin markers make m either 1 or at least 3.

* If m=1, the source marker-one auxiliary bits differ. All old
  marker edges are copied into the target, so the actual target
  twoMeetLevel is exactly 1.
* If m>=3 and m<min(u,a), the source successor full pair types
  must differ. If source m is a 2-split, its exact meet is copied
  unchanged to a target 2-split. If m is an old leaf or 1-split,
  its two normal source pair germs are different, and their
  actual target meet is a fresh pair-event 2-split.
* If m=min(u,a), then m itself is one of the source leaves.
  If the genuine source successor two-types differ, there is
  again a fresh pair-event 2-split. If they agree, the full
  leaf-block transport preserves agreement through f(m), and
  the target meet is capped at min(f(u),f(a))=f(m).

All target leaves are actual old leaf images. These cases prove
the complete target RoleDiary.pair_meets field S2 without source
S1/S2. Combining the already checked target pre-diary and S1
yields the genuine RoleDiary target.

The stronger printed universal old-cut type agreement and
EVERY-FLIP-OF-TARGET absorption property are NOT claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Full S2: every two ordered target leaf pairs meet either at
their minimum first coordinate, marker one, or a genuine
target 2-split. No source S1/S2 assumption is used. -/
theorem onePassRawTarget_pair_meets
    (P : RolePrediary H) :
    ∀ x y z w : Nat, x < y → z < w →
      IsLeaf (onePassRawTarget H) x →
      IsLeaf (onePassRawTarget H) y →
      IsLeaf (onePassRawTarget H) z →
      IsLeaf (onePassRawTarget H) w →
      (onePassRawTarget H).twoMeetLevel x y z w = min x z ∨
      (onePassRawTarget H).twoMeetLevel x y z w = 1 ∨
      IsTwoSplit (onePassRawTarget H)
        ((onePassRawTarget H).twoMeetLevel x y z w) := by
  classical
  intro x y z w hxy hzw hx hy hz hw
  obtain ⟨u,hu,huImage⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H x).mp hx
  obtain ⟨v,hv,hvImage⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H y).mp hy
  obtain ⟨a,ha,haImage⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H z).mp hz
  obtain ⟨b,hb,hbImage⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H w).mp hw
  have hUVImage : onePassOldImage H u < onePassOldImage H v := by
    simpa only [huImage,hvImage] using hxy
  have hABImage : onePassOldImage H a < onePassOldImage H b := by
    simpa only [haImage,hbImage] using hzw
  have huv : u < v := by
    by_contra hn
    have hvu : v ≤ u := by omega
    have hMon := (onePassOldImage_strictMono H).monotone hvu
    omega
  have hab : a < b := by
    by_contra hn
    have hba : b ≤ a := by omega
    have hMon := (onePassOldImage_strictMono H).monotone hba
    omega
  rw [← huImage, ← hvImage, ← haImage, ← hbImage]
  let G := onePassRawTarget H
  let m := H.twoMeetLevel u v a b
  have hSourceMeet : H.twoMeetLevel u v a b = m := rfl
  have hCapBound : m ≤ min u a :=
    H.twoMeetLevel_le_min u v a b
  have hmu : m ≤ u := hCapBound.trans (min_le_left _ _)
  have hma : m ≤ a := hCapBound.trans (min_le_right _ _)
  have hSourceBelow : H.SameTwoTypeBelow m u v a b := by
    change H.SameTwoTypeBelow (H.twoMeetLevel u v a b) u v a b
    exact H.twoMeetLevel_agree u v a b
  have hSourceParent : twoCode H m u v = twoCode H m a b :=
    (twoCode_eq_iff_sameTwoType H m u v a b).mpr hSourceBelow
  rcases P.twoMeet_eq_one_or_ge_three u v a b huv hab hu hv ha hb with
      hOne | hm3
  · have hSourceDiff : ¬ (H.edge 1 u v ↔ H.edge 1 a b) := by
      intro hSame
      have hAgree3 := P.sameMarkerOne_twoTypeBelow_three
        u v a b huv hab hu hv ha hb hSame
      have hBound3 : 3 ≤ min u a := by
        have hu3 := hu.1
        have ha3 := ha.1
        omega
      have hMeetGe : 3 ≤ H.twoMeetLevel u v a b :=
        Nat.le_findGreatest hBound3 hAgree3
      rw [hOne] at hMeetGe
      omega
    have hCopyUV : G.edge 1
        (onePassOldImage H u) (onePassOldImage H v) ↔
        H.edge 1 u v := by
      simpa only [onePassOldImage_one] using
        (onePassRawTarget_edge_image_iff H 1 u v)
    have hCopyAB : G.edge 1
        (onePassOldImage H a) (onePassOldImage H b) ↔
        H.edge 1 a b := by
      simpa only [onePassOldImage_one] using
        (onePassRawTarget_edge_image_iff H 1 a b)
    have hTargetDiff :
        ¬ (G.edge 1 (onePassOldImage H u) (onePassOldImage H v) ↔
            G.edge 1 (onePassOldImage H a) (onePassOldImage H b)) := by
      intro hEq
      exact hSourceDiff (hCopyUV.symm.trans (hEq.trans hCopyAB))
    right
    left
    exact onePassRawTarget_twoMeet_eq_one_of_marker_disagreement
      P (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b)
        ((onePassRawTarget_old_leaf_iff H u).mpr hu)
        ((onePassRawTarget_old_leaf_iff H a).mpr ha)
        hTargetDiff
  · by_cases hCapped : m = min u a
    · have hmLeaf : IsLeaf H m := by
        rcases le_total u a with hua | hau
        · have hmU : m = u := by
            simpa only [min_eq_left hua] using hCapped
          simpa only [hmU] using hu
        · have hmA : m = a := by
            simpa only [min_eq_right hau] using hCapped
          simpa only [hmA] using ha
      have hmNotTwo : ¬ IsTwoSplit H m := by
        intro ht
        exact hmLeaf.2.2 ht.2.2
      by_cases hNext : H.SameTwoTypeBelow (m + 1) u v a b
      · left
        exact onePass_source_leaf_cap_twoMeet_preserved
          P m u v a b hmLeaf hu hv ha hb huv hab
          hmu hma hCapped hSourceMeet hNext
      · have hGermDifferent :
          twoGermCode H m u v ≠ twoGermCode H m a b := by
          intro hEq
          exact hNext ((twoGerm_eq_iff_nextTwoType_of_source_leaf
            P m u v a b hmLeaf hu hv ha hb
            hmu huv hma hab).mp hEq)
        right
        right
        exact onePass_pairBlock_sibling_meet_twoSplit
          P m u v a b hm3 hmNotTwo
          hu hv ha hb hmu hma huv hab
          hSourceParent hGermDifferent
    · have hmu' : m < u := by omega
      have hma' : m < a := by omega
      have hNotNext : ¬ H.SameTwoTypeBelow (m + 1) u v a b := by
        intro hNext
        have hBoundNext : m + 1 ≤ min u a := by omega
        have hPast : m + 1 ≤ H.twoMeetLevel u v a b :=
          Nat.le_findGreatest hBoundNext hNext
        rw [hSourceMeet] at hPast
        omega
      have hGermDifferent :
          twoGermCode H m u v ≠ twoGermCode H m a b := by
        intro hEq
        have huNeM : u ≠ m := by omega
        have haNeM : a ≠ m := by omega
        exact hNotNext
          ((twoGerm_eq_iff_normal H m u v a b
            huNeM haNeM).mp hEq).2
      rcases P.role_valid m hm3 with hmLeaf | hmOne | hmTwo
      · have hmNotTwo : ¬ IsTwoSplit H m := by
          intro ht
          exact hmLeaf.2.2 ht.2.2
        right
        right
        exact onePass_pairBlock_sibling_meet_twoSplit
          P m u v a b hm3 hmNotTwo
          hu hv ha hb hmu hma huv hab
          hSourceParent hGermDifferent
      · have hmNotTwo : ¬ IsTwoSplit H m := by
          intro ht
          exact ht.2.1 hmOne.2.1
        right
        right
        exact onePass_pairBlock_sibling_meet_twoSplit
          P m u v a b hm3 hmNotTwo
          hu hv ha hb hmu hma huv hab
          hSourceParent hGermDifferent
      · have hMeet := onePass_oldTwoSplit_meet_exact
          P m u v a b hmTwo huv hab
            hu hv ha hb hmu' hma' hSourceMeet
        right
        right
        rw [hMeet]
        exact (onePassRawTarget_old_twoSplit_iff H m).mpr hmTwo

/-- The genuine ONE-PASS construction sends every V/E pre-diary to
a full diary: the V/E structure is #634, S1 is #638 and S2 is
proved above. Stronger protected/functorial properties are separate. -/
theorem onePassRawTarget_isDiary
    (P : RolePrediary H) :
    RoleDiary (onePassRawTarget H) :=
  (onePassRawTarget_isPrediary P).withMeets
    (onePassRawTarget_singleton_meets P)
    (onePassRawTarget_pair_meets P)

end DiaryLeafPriority
end ThreeUniformDiaries
