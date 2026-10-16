import ThreeUniformDiaries.DiaryOnePassGlobalOneTypeTransport
import ThreeUniformDiaries.DiaryOnePassGlobalTwoTypeTransport
import ThreeUniformDiaries.DiaryOnePassOriginalSplitTransfer
import ThreeUniformDiaries.DiaryOnePassNonLeafSingletonBlocks

/-!
# Source split meets are retained literally at their old target images

An ORIGINAL 1-split or 2-split must retain its V1/V2 witness in
the one-pass target. We prove this from the full, ACTUAL global
singleton and ordered-pair original-cut transport theorems.

For an old 1-split m and original leaves a,b whose singleton meet
is m, target singleton types agree below f(m), but fail immediately
after f(m). Thus their target singleton meet is EXACTLY f(m).

For an old 2-split m and original ordered leaf pairs P,Q with full
two-type meet m, the same argument gives full target two-type meet
exactly f(m). The block before an original 2-split is empty.

Apply these equalities to the actual source V1/V2 witness pairs to
obtain witnesses at every OLD target 1-split or 2-split. The new split
witnesses are separate and require the default-vs-selected child
separation argument.

No full target V/E/S completion or source S1/S2 is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Exact transport of an existing original 1-split meet to the
same ORIGINAL vertex's target image. -/
theorem onePass_oldOneSplit_meet_exact
    (P : RolePrediary H) (m a b : Nat)
    (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hma : m < a) (hmb : m < b)
    (hMeet : H.oneMeetLevel a b = m) :
    (onePassRawTarget H).oneMeetLevel
       (onePassOldImage H a) (onePassOldImage H b) =
      onePassOldImage H m := by
  classical
  have hSourceAt : H.SameOneTypeBelow m a b := by
    rw [← hMeet]
    exact H.oneMeetLevel_agree a b
  have hSourceNextFail : ¬ H.SameOneTypeBelow (m + 1) a b := by
    intro hnext
    have hCap : m + 1 ≤ min a b := by omega
    have hGreatest : m + 1 ≤ H.oneMeetLevel a b :=
      Nat.le_findGreatest hCap hnext
    omega
  have hGlobal :=
    onePass_global_oneType_transport P m a b
      hm.1 ha hb hma.le hmb.le
  have hNotLeaf : ¬ IsLeaf H m := by
    intro h
    exact h.2.1 hm.2.1
  have hBlock :=
    onePassBlock_oneType_unchanged_of_not_leaf P m
      (onePassOldImage H a) (onePassOldImage H b) hNotLeaf
  have hBeforeOld :
      H.SameOneTypeBelow m a b ↔
        (onePassRawTarget H).SameOneTypeBelow
          (onePassOldImage H m)
          (onePassOldImage H a) (onePassOldImage H b) :=
    hGlobal.trans hBlock.symm
  have hTargetAt := hBeforeOld.mp hSourceAt
  have hStep :=
    onePass_original_oneSplit_type_transfer P m a b hm hBeforeOld
  have hTargetNextFail :
      ¬ (onePassRawTarget H).SameOneTypeBelow
          (onePassOldImage H m + 1)
          (onePassOldImage H a) (onePassOldImage H b) := by
    intro hnext
    exact hSourceNextFail (hStep.mpr hnext)
  have hmaTarget :
      onePassOldImage H m < onePassOldImage H a :=
    (onePassOldImage_strictMono H) hma
  have hmbTarget :
      onePassOldImage H m < onePassOldImage H b :=
    (onePassOldImage_strictMono H) hmb
  have hCap :
      onePassOldImage H m ≤
        min (onePassOldImage H a) (onePassOldImage H b) := by
    omega
  have hLower :
      onePassOldImage H m ≤
        (onePassRawTarget H).oneMeetLevel
          (onePassOldImage H a) (onePassOldImage H b) :=
    Nat.le_findGreatest hCap hTargetAt
  have hUpper :
      (onePassRawTarget H).oneMeetLevel
          (onePassOldImage H a) (onePassOldImage H b) <
        onePassOldImage H m + 1 := by
    by_contra hNot
    have hGe :
        onePassOldImage H m + 1 ≤
          (onePassRawTarget H).oneMeetLevel
            (onePassOldImage H a) (onePassOldImage H b) := by omega
    have hAgree :=
      (onePassRawTarget H).oneMeetLevel_agree
        (onePassOldImage H a) (onePassOldImage H b)
    have hNext :
        (onePassRawTarget H).SameOneTypeBelow
          (onePassOldImage H m + 1)
          (onePassOldImage H a) (onePassOldImage H b) := by
      intro x y hxy hy
      exact hAgree hxy (by omega)
    exact hTargetNextFail hNext
  omega

/-- Exact transport of an existing original 2-split full
ordered-pair meet to its actual target image. -/
theorem onePass_oldTwoSplit_meet_exact
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsTwoSplit H m)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m < a) (hmc : m < c)
    (hMeet : H.twoMeetLevel a b c d = m) :
    (onePassRawTarget H).twoMeetLevel
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) =
      onePassOldImage H m := by
  classical
  have hSourceAt : H.SameTwoTypeBelow m a b c d := by
    rw [← hMeet]
    exact H.twoMeetLevel_agree a b c d
  have hSourceNextFail : ¬ H.SameTwoTypeBelow (m + 1) a b c d := by
    intro hNext
    have hCap : m + 1 ≤ min a c := by omega
    have hGreatest : m + 1 ≤ H.twoMeetLevel a b c d :=
      Nat.le_findGreatest hCap hNext
    omega
  have hGlobal :=
    onePass_global_twoType_transport P m a b c d
      hm.1 ha hb hc hd hab hcd hma.le hmc.le
  have hNotLeaf : ¬ IsLeaf H m := by
    intro h
    exact h.2.2 hm.2.2
  have hNotSmall : ¬ m < 3 := by
    have h3 := hm.1
    omega
  have hEmpty : onePassBlock H m = [] := by
    simp [onePassBlock,hNotSmall,hm,hNotLeaf]
  have hCut : onePassOldImage H m = onePassBefore H m := by
    simp [onePassOldImage,onePassBlockSize,hEmpty]
  have hBeforeOld :
      H.SameTwoTypeBelow m a b c d ↔
        (onePassRawTarget H).SameTwoTypeBelow
          (onePassOldImage H m)
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) := by
    simpa only [hCut] using hGlobal
  have hTargetAt := hBeforeOld.mp hSourceAt
  have hStep :=
    onePass_original_twoSplit_type_transfer P m a b c d hm hBeforeOld
  have hTargetNextFail :
      ¬ (onePassRawTarget H).SameTwoTypeBelow
          (onePassOldImage H m + 1)
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) := by
    intro hNext
    exact hSourceNextFail (hStep.mpr hNext)
  have hmaTarget :
      onePassOldImage H m < onePassOldImage H a :=
    (onePassOldImage_strictMono H) hma
  have hmcTarget :
      onePassOldImage H m < onePassOldImage H c :=
    (onePassOldImage_strictMono H) hmc
  have hCap :
      onePassOldImage H m ≤
        min (onePassOldImage H a) (onePassOldImage H c) := by
    omega
  have hLower :
      onePassOldImage H m ≤
        (onePassRawTarget H).twoMeetLevel
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) :=
    Nat.le_findGreatest hCap hTargetAt
  have hUpper :
      (onePassRawTarget H).twoMeetLevel
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) <
        onePassOldImage H m + 1 := by
    by_contra hNot
    have hGe :
        onePassOldImage H m + 1 ≤
          (onePassRawTarget H).twoMeetLevel
            (onePassOldImage H a) (onePassOldImage H b)
            (onePassOldImage H c) (onePassOldImage H d) := by omega
    have hAgree :=
      (onePassRawTarget H).twoMeetLevel_agree
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)
    have hNext :
        (onePassRawTarget H).SameTwoTypeBelow
          (onePassOldImage H m + 1)
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact hAgree.1 hxy (by omega)
      · intro x y hxy hy
        exact hAgree.2.1 hxy (by omega)
      · intro x hx
        exact hAgree.2.2 (by omega)
    exact hTargetNextFail hNext
  omega

/-- Existing source V1 split witnesses remain EXACT split-meet
witnesses at their original target 1-split image. -/
theorem onePass_oldOneSplit_has_witness
    (P : RolePrediary H) (m : Nat) (hm : IsOneSplit H m) :
    ∃ a b : Nat,
      IsLeaf (onePassRawTarget H) a ∧
      IsLeaf (onePassRawTarget H) b ∧
      onePassOldImage H m < a ∧
      onePassOldImage H m < b ∧
      (onePassRawTarget H).oneMeetLevel a b =
        onePassOldImage H m := by
  obtain ⟨a,b,ha,hb,hma,hmb,hMeet⟩ :=
    P.one_split_witness m hm
  refine ⟨onePassOldImage H a,onePassOldImage H b,
    (onePassRawTarget_old_leaf_iff H a).mpr ha,
    (onePassRawTarget_old_leaf_iff H b).mpr hb,
    (onePassOldImage_strictMono H) hma,
    (onePassOldImage_strictMono H) hmb,
    onePass_oldOneSplit_meet_exact P m a b hm ha hb hma hmb hMeet⟩

/-- Existing source V2 split witnesses retain their exact
complete ordered-pair meet at the original target 2-split image. -/
theorem onePass_oldTwoSplit_has_witness
    (P : RolePrediary H) (m : Nat) (hm : IsTwoSplit H m) :
    ∃ a b c d : Nat, a < b ∧ c < d ∧
      IsLeaf (onePassRawTarget H) a ∧
      IsLeaf (onePassRawTarget H) b ∧
      IsLeaf (onePassRawTarget H) c ∧
      IsLeaf (onePassRawTarget H) d ∧
      onePassOldImage H m < a ∧
      onePassOldImage H m < c ∧
      (onePassRawTarget H).twoMeetLevel a b c d =
        onePassOldImage H m := by
  obtain ⟨a,b,c,d,hab,hcd,ha,hb,hc,hd,hma,hmc,hMeet⟩ :=
    P.two_split_witness m hm
  refine ⟨onePassOldImage H a,onePassOldImage H b,
    onePassOldImage H c,onePassOldImage H d,
    (onePassOldImage_strictMono H) hab,
    (onePassOldImage_strictMono H) hcd,
    (onePassRawTarget_old_leaf_iff H a).mpr ha,
    (onePassRawTarget_old_leaf_iff H b).mpr hb,
    (onePassRawTarget_old_leaf_iff H c).mpr hc,
    (onePassRawTarget_old_leaf_iff H d).mpr hd,
    (onePassOldImage_strictMono H) hma,
    (onePassOldImage_strictMono H) hmc,
    onePass_oldTwoSplit_meet_exact P m a b c d
      hm hab hcd ha hb hc hd hma hmc hMeet⟩

end DiaryLeafPriority
end ThreeUniformDiaries
