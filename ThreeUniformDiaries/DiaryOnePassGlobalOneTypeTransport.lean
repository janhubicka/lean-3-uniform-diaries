import ThreeUniformDiaries.DiaryOnePassNonLeafSingletonBlocks
import ThreeUniformDiaries.DiaryOnePassOldLeafColumnStability
import ThreeUniformDiaries.DiaryOnePassLeafBlockTransport
import ThreeUniformDiaries.DiaryOnePassOriginalSplitTransfer

/-!
# Global singleton-type transport across ALL original one-pass cuts

This is the genuine singleton half of the corrected one-pass pre-diary
completion transport theorem. For every original cut m>=3, and ANY
source leaves u,v at or above m, equality of source singleton types
below m is equivalent to equality of their ACTUAL target singleton
types below the beginning of the finite event block B_m.

The argument is an induction on the ORIGINAL source cut m, never
on the moving target index. It uses the exact target edge relation,
not a synthetic type-code model. The three cases of the original
vertex role are:

* old 1-split: no singleton events in B_m, then the original
  zero-marker bit is copied exactly;
* old 2-split: no singleton event and no singleton middle-column bit;
* old leaf: the events of B_m split exactly the source normal/terminal
  singleton germs and delayed earlier pair-event incidences in the
  target old leaf's column factor through the next source type.

This transports ORIGINAL singleton type partitions, only at their
appropriate original source cuts and for source leaves above the cut.
It does NOT imply the false universal old-cut preservation statement
printed in the manuscript, does not prove auxiliary pair transport,
and does not assert V/E/S completion or flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

variable {H : Ordered3Graph Nat}

/-- One complete induction step, from the start of B_m to
the start of B_(m+1), for original leaves strictly above m. -/
theorem onePass_oneType_originalCut_succ
    (P : RolePrediary H) (m u v : Nat)
    (hm : 3 ≤ m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m < u) (hmv : m < v)
    (hBefore : H.SameOneTypeBelow m u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v)) :
    H.SameOneTypeBelow (m + 1) u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H (m + 1))
        (onePassOldImage H u) (onePassOldImage H v) := by
  rw [onePassBefore_succ H m]
  rcases P.role_valid m hm with hLeaf | hOne | hTwo
  · have hBlock :=
      onePass_leafBlock_oneType_transfer P m u v hLeaf
        hu hv hmu.le hmv.le hBefore
    rw [(onePassRawTarget H).sameOneTypeBelow_succ_iff
      (onePassOldImage H m)
      (onePassOldImage H u) (onePassOldImage H v)]
    constructor
    · intro hNext
      refine ⟨hBlock.mp hNext, ?_⟩
      exact onePass_oldLeaf_column_stable_of_nextOneType
        P m u v hLeaf hu hv hmu hmv hNext
    · rintro ⟨hTargetBefore, _⟩
      exact hBlock.mpr hTargetBefore
  · have hNotLeaf : ¬ IsLeaf H m := by
      intro h
      exact h.2.1 hOne.2.1
    have hNoBlock :
        (onePassRawTarget H).SameOneTypeBelow
          (onePassOldImage H m)
          (onePassOldImage H u) (onePassOldImage H v) ↔
        (onePassRawTarget H).SameOneTypeBelow
          (onePassBefore H m)
          (onePassOldImage H u) (onePassOldImage H v) :=
      onePassBlock_oneType_unchanged_of_not_leaf P m
        (onePassOldImage H u) (onePassOldImage H v) hNotLeaf
    have hBeforeOld :
        H.SameOneTypeBelow m u v ↔
        (onePassRawTarget H).SameOneTypeBelow
          (onePassOldImage H m)
          (onePassOldImage H u) (onePassOldImage H v) :=
      hBefore.trans hNoBlock.symm
    exact onePass_original_oneSplit_type_transfer
      P m u v hOne hBeforeOld
  · have hNotLeaf : ¬ IsLeaf H m := by
      intro h
      exact h.2.2 hTwo.2.2
    have hNoBlock :
        (onePassRawTarget H).SameOneTypeBelow
          (onePassOldImage H m)
          (onePassOldImage H u) (onePassOldImage H v) ↔
        (onePassRawTarget H).SameOneTypeBelow
          (onePassBefore H m)
          (onePassOldImage H u) (onePassOldImage H v) :=
      onePassBlock_oneType_unchanged_of_not_leaf P m
        (onePassOldImage H u) (onePassOldImage H v) hNotLeaf
    have hSource :
        H.SameOneTypeBelow (m + 1) u v ↔
        H.SameOneTypeBelow m u v := by
      rw [H.sameOneTypeBelow_succ_iff m u v]
      constructor
      · exact And.left
      · intro h
        refine ⟨h, ?_⟩
        intro z hz
        exact iff_of_false
          (P.twoSplit_no_middle m z u hTwo)
          (P.twoSplit_no_middle m z v hTwo)
    have hTarget :=
      onePass_original_twoSplit_nextOneCut P m u v hTwo
    calc
      H.SameOneTypeBelow (m + 1) u v ↔
          H.SameOneTypeBelow m u v := hSource
      _ ↔ (onePassRawTarget H).SameOneTypeBelow
          (onePassBefore H m)
          (onePassOldImage H u) (onePassOldImage H v) := hBefore
      _ ↔ (onePassRawTarget H).SameOneTypeBelow
          (onePassOldImage H m)
          (onePassOldImage H u) (onePassOldImage H v) :=
        hNoBlock.symm
      _ ↔ (onePassRawTarget H).SameOneTypeBelow
          (onePassOldImage H m + 1)
          (onePassOldImage H u) (onePassOldImage H v) :=
        hTarget.symm

/-- UNCONDITIONAL global singleton-type transport at all original
source cuts, for the concrete raw target and actual source leaves.

At original cut m the corresponding target cut is the start of
B_m; subsequent event positions are accounted for precisely by
the next source-cut induction step, including terminal germs. -/
theorem onePass_global_oneType_transport
    (P : RolePrediary H) (m u v : Nat)
    (hm : 3 ≤ m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v) :
    H.SameOneTypeBelow m u v ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v) := by
  have hAll :
      ∀ k : Nat, ∀ u v : Nat,
        IsLeaf H u → IsLeaf H v →
        k + 3 ≤ u → k + 3 ≤ v →
        (H.SameOneTypeBelow (k + 3) u v ↔
         (onePassRawTarget H).SameOneTypeBelow
           (onePassBefore H (k + 3))
           (onePassOldImage H u) (onePassOldImage H v)) := by
    intro k
    induction k with
    | zero =>
      intro u v hu hv hku hkv
      have hBefore3 : onePassBefore H 3 = 3 := by
        simpa using (onePassBefore_succ H 2)
      simpa only [Nat.zero_add, hBefore3] using
        (onePass_oneTypeBelow_three_iff H u v)
    | succ k ih =>
      intro u v hu hv hku hkv
      have hPrev := ih u v hu hv (by omega) (by omega)
      have hNext :=
        onePass_oneType_originalCut_succ P (k + 3) u v
          (by omega) hu hv (by omega) (by omega) hPrev
      have hs : k + 3 + 1 = Nat.succ k + 3 := by omega
      simpa only [hs] using hNext
  have hIndex : m - 3 + 3 = m := by omega
  simpa only [hIndex] using
    (hAll (m - 3) u v hu hv (by omega) (by omega))

end DiaryLeafPriority
end ThreeUniformDiaries
