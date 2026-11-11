import ThreeUniformDiaries.DiaryInfiniteHighOneSplitCone
import ThreeUniformDiaries.DiaryHighTwoSidedE3RangeWitness

/-!
# Track D: genuine joint high E2/E3 geometry on four prescribed leaves

In an arbitrary injective genuine-leaf range, the high two-sided E3
witness theorem may be applied INSIDE an infinite monochromatic
singleton cone. Thus all six singleton meets of its four leaves are
actual high one-splits, while the two ordered leaf pairs split at
an actual high E3 two-split. The two constituent pairs automatically
witness both E2 sides at their respective one-splits.

No split image is prescribed in advance. This proves simultaneous
UNROOTED finite geometry, not a relative extension of a fixed stage,
and gives no future order reserve or countable-source unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- In EVERY injective enumeration of genuine target leaves, there
are four leaves witnessing opposite E3 branches at a high two-split.
The same four leaves have all six S1 meets high, and the first and
second ordered pairs each witness opposite E2 branches at their own
high one-split. No old support, old split image, or branch sign is
prescribed. The outer enumeration F need not be increasing. -/
theorem RoleDiary.exists_joint_high_E2_E3_four_leaf_witness
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInj : Function.Injective F)
    (hLeaves : ∀ n : Nat, IsLeaf K (F n))
    (B N : Nat) :
    ∃ i j k l s t u : Nat,
      N ≤ i ∧ i < j ∧ j < k ∧ k < l ∧
      F i < F j ∧ F k < F l ∧
      B ≤ s ∧ B ≤ t ∧ B ≤ u ∧
      IsOneSplit K s ∧ IsOneSplit K t ∧ IsTwoSplit K u ∧
      K.oneMeetLevel (F i) (F j) = s ∧
      K.oneMeetLevel (F k) (F l) = t ∧
      K.twoMeetLevel (F i) (F j) (F k) (F l) = u ∧
      B ≤ K.oneMeetLevel (F i) (F k) ∧
      B ≤ K.oneMeetLevel (F i) (F l) ∧
      B ≤ K.oneMeetLevel (F j) (F k) ∧
      B ≤ K.oneMeetLevel (F j) (F l) ∧
      ((K.edge 0 s (F i) ∧ ¬ K.edge 0 s (F j)) ∨
       (¬ K.edge 0 s (F i) ∧ K.edge 0 s (F j))) ∧
      ((K.edge 0 t (F k) ∧ ¬ K.edge 0 t (F l)) ∨
       (¬ K.edge 0 t (F k) ∧ K.edge 0 t (F l))) ∧
      ((K.edge u (F i) (F j) ∧ ¬ K.edge u (F k) (F l)) ∨
       (¬ K.edge u (F i) (F j) ∧ K.edge u (F k) (F l))) := by
  classical
  obtain ⟨I, hI, hInitial, hPair⟩ :=
    DK.exists_infinite_high_oneSplit_cone F hInj hLeaves B B N
  have hFI : Function.Injective (fun n : Nat => F (I n)) :=
    hInj.comp hI.injective
  have hLeafI (n : Nat) : IsLeaf K (F (I n)) := hLeaves (I n)
  obtain ⟨a, b, c, d, u, _ha, hab, hbc, hcd,
          hFab, hFcd, hBu, hTwo, hMeetU, _hua, _huc, hE3⟩ :=
    DK.exists_high_two_sided_E3_split_in_leaf_range
      (fun n => F (I n)) hFI hLeafI B 0
  have hac : a < c := lt_trans hab hbc
  have had : a < d := lt_trans hac hcd
  have hbd : b < d := lt_trans hbc hcd
  let s := K.oneMeetLevel (F (I a)) (F (I b))
  let t := K.oneMeetLevel (F (I c)) (F (I d))
  have hOneS : IsOneSplit K s := (hPair a b hab).2.1
  have hOneT : IsOneSplit K t := (hPair c d hcd).2.1
  have hBs : B ≤ s := (hPair a b hab).2.2
  have hBt : B ≤ t := (hPair c d hcd).2.2
  have hCapS : s ≤ min (F (I a)) (F (I b)) :=
    K.oneMeetLevel_le_min (F (I a)) (F (I b))
  have hCapT : t ≤ min (F (I c)) (F (I d)) :=
    K.oneMeetLevel_le_min (F (I c)) (F (I d))
  have hSnotA : s ≠ F (I a) := by
    intro heq
    have hRole : IsOneSplit K (F (I a)) := heq ▸ hOneS
    exact (hLeaves (I a)).2.1 hRole.2.1
  have hTnotC : t ≠ F (I c) := by
    intro heq
    have hRole : IsOneSplit K (F (I c)) := heq ▸ hOneT
    exact (hLeaves (I c)).2.1 hRole.2.1
  have hSleA : s ≤ F (I a) := hCapS.trans (min_le_left _ _)
  have hTleC : t ≤ F (I c) := hCapT.trans (min_le_left _ _)
  have hSa : s < F (I a) := by omega
  have hSb : s < F (I b) := by omega
  have hTc : t < F (I c) := by omega
  have hTd : t < F (I d) := by omega
  have hOppS :
      ¬ (K.edge 0 s (F (I a)) ↔ K.edge 0 s (F (I b))) :=
    DK.oneSplit_witness_opposite_marker s (F (I a)) (F (I b))
      hOneS (hLeaves (I a)) (hLeaves (I b)) hSa hSb rfl
  have hOppT :
      ¬ (K.edge 0 t (F (I c)) ↔ K.edge 0 t (F (I d))) :=
    DK.oneSplit_witness_opposite_marker t (F (I c)) (F (I d))
      hOneT (hLeaves (I c)) (hLeaves (I d)) hTc hTd rfl
  refine ⟨I a, I b, I c, I d, s, t, u,
    (hInitial a).1, hI hab, hI hbc, hI hcd, hFab, hFcd,
    hBs, hBt, hBu, hOneS, hOneT, hTwo, rfl, rfl, hMeetU,
    (hPair a c hac).2.2, (hPair a d had).2.2,
    (hPair b c hbc).2.2, (hPair b d hbd).2.2, ?_, ?_, hE3⟩
  · tauto
  · tauto

end DiaryLeafPriority
end ThreeUniformDiaries
