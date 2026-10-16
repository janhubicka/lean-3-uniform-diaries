import ThreeUniformDiaries.DiaryOnePassFreshSuccessorCuts
import ThreeUniformDiaries.DiaryPrediaryRoleNextCut

/-!
# Exact original-split successor-cut transfer in the one-pass target

The full original-cut transport induction visits all fresh events in
B_m and then the original vertex f(m). At a source 1-split or 2-split,
the original vertex itself is an actual target split, with exactly
the same marker-defined role and the same incidence bit(s).

This file proves the *original vertex step* on the concrete target:
at an original 1-split, the new singleton cut is old target type
agreement plus precisely the original source bit E(0,m,u);
at an original 2-split, the new complete pair type is old target
agreement plus E(m,a,b), and singleton agreement is unchanged.

As a consequence, if source and target type partitions agree at
the cut just before the image of an old split, they agree at the
successor cut just after that vertex. The results only assume
RolePrediary V/E, not S1/S2 or any global induction hypothesis.

The fresh event block B_m, the old LEAF case, and the full
across-block prefix induction remain separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

variable {H : Ordered3Graph Nat}

/-- Passing an original source 1-split image in the target adds
exactly the *original* incidence with zero marker. -/
theorem onePass_original_oneSplit_nextOneCut
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsOneSplit H m) :
    (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m + 1)
        (onePassOldImage H u) (onePassOldImage H v) ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H u) (onePassOldImage H v) ∧
      (H.edge 0 m u ↔ H.edge 0 m v) := by
  have hrole : IsOneSplit (onePassRawTarget H)
      (onePassOldImage H m) :=
    (onePassRawTarget_old_oneSplit_iff H m).mpr hm
  have htarget :=
    onePassRawTarget_oneSplit_sameOneType_succ_iff P
      (onePassOldImage H m) (onePassOldImage H u)
      (onePassOldImage H v) hrole
  have heU : (onePassRawTarget H).edge 0
      (onePassOldImage H m) (onePassOldImage H u) ↔
      H.edge 0 m u := by
    simpa only [onePassOldImage_zero] using
      (onePassRawTarget_edge_image_iff H 0 m u)
  have heV : (onePassRawTarget H).edge 0
      (onePassOldImage H m) (onePassOldImage H v) ↔
      H.edge 0 m v := by
    simpa only [onePassOldImage_zero] using
      (onePassRawTarget_edge_image_iff H 0 m v)
  simpa only [heU, heV] using htarget

/-- Passing an original source 2-split in the target introduces
no new singleton middle-column test. -/
theorem onePass_original_twoSplit_nextOneCut
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsTwoSplit H m) :
    (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m + 1)
        (onePassOldImage H u) (onePassOldImage H v) ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H u) (onePassOldImage H v) := by
  exact onePassRawTarget_twoSplit_sameOneType_succ_iff P
    (onePassOldImage H m) (onePassOldImage H u)
    (onePassOldImage H v)
    ((onePassRawTarget_old_twoSplit_iff H m).mpr hm)

/-- Passing an original 2-split image adds exactly its ORIGINAL
auxiliary source bit; no extra singleton-coordinate test appears. -/
theorem onePass_original_twoSplit_nextTwoCut
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsTwoSplit H m) :
    (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m + 1)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) ∧
      (H.edge m a b ↔ H.edge m c d) := by
  have hrole : IsTwoSplit (onePassRawTarget H)
      (onePassOldImage H m) :=
    (onePassRawTarget_old_twoSplit_iff H m).mpr hm
  have htarget :=
    onePassRawTarget_twoSplit_sameTwoType_succ_iff P
      (onePassOldImage H m)
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) hrole
  have heAB : (onePassRawTarget H).edge
      (onePassOldImage H m) (onePassOldImage H a)
      (onePassOldImage H b) ↔ H.edge m a b :=
    onePassRawTarget_edge_image_iff H m a b
  have heCD : (onePassRawTarget H).edge
      (onePassOldImage H m) (onePassOldImage H c)
      (onePassOldImage H d) ↔ H.edge m c d :=
    onePassRawTarget_edge_image_iff H m c d
  simpa only [heAB, heCD] using htarget

/-- If singleton partitions agree immediately BEFORE the old
1-split, then they also agree immediately AFTER that split.
This is the precise local induction step for old 1-split vertices. -/
theorem onePass_original_oneSplit_type_transfer
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsOneSplit H m)
    (hbefore : H.SameOneTypeBelow m u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H u) (onePassOldImage H v)) :
    H.SameOneTypeBelow (m + 1) u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m + 1)
        (onePassOldImage H u) (onePassOldImage H v) := by
  rw [P.oneSplit_sameOneType_succ_iff m u v hm,
      onePass_original_oneSplit_nextOneCut P m u v hm]
  exact and_congr hbefore Iff.rfl

/-- The corresponding original 2-split successor step for
COMPLETE ordered pair types (both coordinate one-types plus
the auxiliary pair-type tests). -/
theorem onePass_original_twoSplit_type_transfer
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsTwoSplit H m)
    (hbefore : H.SameTwoTypeBelow m a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)) :
    H.SameTwoTypeBelow (m + 1) a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m + 1)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  rw [P.twoSplit_sameTwoType_succ_iff m a b c d hm,
      onePass_original_twoSplit_nextTwoCut P m a b c d hm]
  exact and_congr hbefore Iff.rfl

end DiaryLeafPriority
end ThreeUniformDiaries
