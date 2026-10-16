import ThreeUniformDiaries.DiaryOnePassBlockGermTransport
import ThreeUniformDiaries.DiaryOnePassSourceGermSuccessors

/-!
# Genuine singleton type-transport induction step through a leaf block

For two original leaves u,v surviving source cut m, suppose the
singleton partition is transported exactly immediately BEFORE B_m:
  SourceSameOne(m,u,v) iff TargetSameOne(before B_m,f(u),f(v)).

When the ORIGINAL vertex m is itself a leaf, the event block
separates precisely the normal/terminal singleton germs, and those
source germ classes are EXACTLY the original singleton (m+1)-types.

Hence the transport property after ALL events of B_m is:
  SourceSameOne(m+1,u,v) iff TargetSameOne(f(m),f(u),f(v)).

This is a real conditional local induction step on the concrete
target. It handles u=m and v=m as well as the later normal leaves.
It makes NO preservation assumption about arbitrary old type
agreements, which is the false clause in the printed lemma.

Remaining to complete the global induction: show passing the old
LEAF vertex f(m) does not create additional distinctions beyond
those germ classes, and combine this with the source split cases
and the full pair-type block induction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- If the initial parent singleton partition agrees before B_m,
then the original successor singleton partition agrees exactly
after B_m, whenever original m is a leaf. -/
theorem onePass_leafBlock_oneType_transfer
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsLeaf H m) (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hbefore : H.SameOneTypeBelow m u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v)) :
    H.SameOneTypeBelow (m + 1) u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H u) (onePassOldImage H v) := by
  constructor
  · intro hNext
    have hParent : H.SameOneTypeBelow m u v := by
      intro a b hab hb
      exact hNext hab (by omega)
    have hCode : oneCode H m u = oneCode H m v :=
      (oneCode_eq_iff_sameOneType H m u v).mpr hParent
    have hGerm : oneGermCode H m u = oneGermCode H m v :=
      (oneGerm_eq_iff_nextOneType_of_source_leaf
        P m u v hm hu hv hmu hmv).mpr hNext
    exact (onePassBlock_oneType_refinement_iff
      P m u v hm hu hv hmu hmv hCode).mpr
      ⟨hbefore.mp hParent, hGerm⟩
  · intro hAfter
    have hStart : (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v) :=
      ((onePassBlock_oneType_interval_iff H m
        (onePassOldImage H u) (onePassOldImage H v)).mp hAfter).1
    have hParent : H.SameOneTypeBelow m u v := hbefore.mpr hStart
    have hCode : oneCode H m u = oneCode H m v :=
      (oneCode_eq_iff_sameOneType H m u v).mpr hParent
    have hGerm : oneGermCode H m u = oneGermCode H m v :=
      ((onePassBlock_oneType_refinement_iff
        P m u v hm hu hv hmu hmv hCode).mp hAfter).2
    exact (oneGerm_eq_iff_nextOneType_of_source_leaf
      P m u v hm hu hv hmu hmv).mp hGerm

end DiaryLeafPriority
end ThreeUniformDiaries
