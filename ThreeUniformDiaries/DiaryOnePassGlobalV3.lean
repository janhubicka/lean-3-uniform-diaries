import ThreeUniformDiaries.DiaryOnePassLeafSiblingLex
import ThreeUniformDiaries.DiaryOnePassSourceLeafMeetRoles
import ThreeUniformDiaries.DiaryOnePassOldOneSplitLex
import ThreeUniformDiaries.DiaryOnePassV3Reduction

/-!
# COMPLETE target Devlin V3 marker clauses of the actual one-pass target

For any two ordered original source leaves a<b, put
m = oneMeetLevel_H(a,b). Source V/E already guarantees m>=3
and that its role is either a true leaf or a true 1-split,
with no source S1/S2 hypothesis.

If m is a source leaf, the source singleton germs have a
common m-parent and MUST be different: otherwise the next-cut
types would agree and contradict maximality of m, while the
terminal capped case is disjoint from normal germs. The verified
real selected/default child partition and strict indexed rank
scheduler preserve LexEarlier in this case.

If m is an existing source 1-split, the source/target zero
incidence bits agree and exact old one-meet transport preserves
the genuine LexEarlier comparator (#628).

This establishes the literal global old-leaf comparison required
by #608, and therefore BOTH target V3 marker equivalences for
every true target leaf pair. It does not claim S1/S2 or full
diary/flip completion.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Source vertices with a given actual singleton meet have
distinct successor/terminal singleton germs at that cut.
This is the exact counterpart of maximality of oneMeetLevel;
no pre-diary assumptions are necessary. -/
theorem onePass_firstOneMeet_trueGerms_distinct
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hNe : u ≠ v)
    (hMeet : H.oneMeetLevel u v = m) :
    oneGermCode H m u ≠ oneGermCode H m v := by
  classical
  by_cases hu : u = m
  · subst u
    have hvNe : v ≠ m := by
      intro heq
      apply hNe
      simpa [heq]
    exact oneGerm_terminal_ne_normal H m v hvNe
  · have hmu' : m < u := by omega
    by_cases hv : v = m
    · subst v
      exact (oneGerm_terminal_ne_normal H m u hu).symm
    · have hmv' : m < v := by omega
      intro hGerm
      have hNext : H.SameOneTypeBelow (m + 1) u v :=
        ((oneGerm_eq_iff_normal H m u v hu hv).mp hGerm).2
      have hBound : m + 1 ≤ min u v := by omega
      have hTooFar : m + 1 ≤ H.oneMeetLevel u v :=
        Nat.le_findGreatest hBound hNext
      rw [hMeet] at hTooFar
      omega

/-- The ACTUAL one-pass embedding preserves the manuscript's
numerical LexEarlier relation on EVERY pair of original leaves.
This is the complete source-order theorem deferred by #608. -/
theorem onePass_preserves_sourceLex
    (P : RolePrediary H) :
    OnePassPreservesSourceLex H := by
  intro a b hab ha hb
  let m := H.oneMeetLevel a b
  have hCap : m ≤ min a b := H.oneMeetLevel_le_min a b
  have hma : m ≤ a := hCap.trans (min_le_left _ _)
  have hmb : m ≤ b := hCap.trans (min_le_right _ _)
  rcases onePass_source_leafOneMeet_is_leaf_or_oneSplit
      P a b ha hb with hmLeaf | hmOne
  · have hParent : oneCode H m a = oneCode H m b :=
      (oneCode_eq_iff_sameOneType H m a b).mpr (by
        change H.SameOneTypeBelow (H.oneMeetLevel a b) a b
        exact H.oneMeetLevel_agree a b)
    have hGermNe : oneGermCode H m a ≠
        oneGermCode H m b :=
      onePass_firstOneMeet_trueGerms_distinct
        H m a b hma hmb (by omega) rfl
    exact onePass_leafBlock_siblings_preserve_sourceLex
      P m a b hmLeaf ha hb hma hmb hParent hGermNe
  · have hma' : m < a := by
      have hNotEq : m ≠ a := by
        intro heq
        have hSplitA : IsOneSplit H a := by
          have hMeetEq : H.oneMeetLevel a b = a := heq
          simpa only [hMeetEq] using hmOne
        exact ha.2.1 hSplitA.2.1
      omega
    have hmb' : m < b := by omega
    exact onePass_oldOneSplit_preserves_sourceLex
      P m a b hmOne ha hb hma' hmb' rfl

/-- Both literal V3 marker clauses are true on ALL actual target
leaves. This does not assume any target diary axiom: it is the
verified source order comparison plus #608's full target leaf census
and exact copied old marker edges. -/
theorem onePassRawTarget_complete_V3
    (P : RolePrediary H) :
    OnePassTargetV3 H :=
  (onePassTargetV3_iff_sourceLex P).mpr
    (onePass_preserves_sourceLex P)

end DiaryLeafPriority
end ThreeUniformDiaries
