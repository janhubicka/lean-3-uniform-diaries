import ThreeUniformDiaries.DiaryUnboundedOneSplitsFromRange
import ThreeUniformDiaries.DiaryOneSplitWitnessClasses

/-!
# Track D: high genuine E2 branch pairs in every injected leaf range

The verified unbounded-S1-meet theorem in a genuine RoleDiary gives
arbitrarily high one-splits witnessed by two selected leaves of any
injected infinite genuine-leaf range, regardless of its enumeration.

The actual E/V1 diary structure says the two leaves witnessing their
common singleton split must have opposite edge(0,s,leaf) bits:
one lies on the positive and the other on the negative E2 branch.

Therefore a prescribed unordered leaf range has arbitrarily high
new genuine one-split levels at which BOTH E2 orientations occur
inside the range. The split level and the two leaves are CHOSEN
together. This does not let us prescribe an old source one-split's
already-fixed target image, or simultaneous E2/E3 constraints at
a compatible old support, or future-order reserve.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For every numerical split cutoff B and outer input cutoff N,
there is a genuine one-split s ≥ B and two leaves from the original
unordered injected range, with later input indices i<j, whose
singleton meet is exactly s. The split is genuinely TWO-SIDED:
one witness has E2 marker edge (0,s,-) and the other does not.

No prescribed old support or uniform branch choice is assumed. -/
theorem RoleDiary.exists_high_two_sided_E2_split_in_leaf_range
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInj : Function.Injective F)
    (hLeaves : ∀ i : Nat, IsLeaf K (F i))
    (B N : Nat) :
    ∃ i j s : Nat,
      N ≤ i ∧ i < j ∧ B ≤ s ∧
      IsOneSplit K s ∧
      K.oneMeetLevel (F i) (F j) = s ∧
      s < F i ∧ s < F j ∧
      ((K.edge 0 s (F i) ∧ ¬ K.edge 0 s (F j)) ∨
       (¬ K.edge 0 s (F i) ∧ K.edge 0 s (F j))) := by
  classical
  obtain ⟨i, j, hi, hij, hHigh, hSplit⟩ :=
    DK.exists_arbitrarily_high_oneSplit_in_injective_leaf_range
      F hInj hLeaves B N
  let s := K.oneMeetLevel (F i) (F j)
  have hs : IsOneSplit K s := hSplit
  have hNe : F i ≠ F j := by
    intro h
    exact (ne_of_lt hij) (hInj h)
  have hBound : s ≤ min (F i) (F j) := by
    exact K.oneMeetLevel_le_min (F i) (F j)
  have hNeI : s ≠ F i := by
    intro hEq
    have hBad : IsOneSplit K (F i) := by
      simpa only [hEq] using hs
    exact (hLeaves i).2.1 hBad.2.1
  have hNeJ : s ≠ F j := by
    intro hEq
    have hBad : IsOneSplit K (F j) := by
      simpa only [hEq] using hs
    exact (hLeaves j).2.1 hBad.2.1
  have hSi : s < F i := by omega
  have hSj : s < F j := by omega
  have hOpp :
      ¬ (K.edge 0 s (F i) ↔ K.edge 0 s (F j)) :=
    DK.oneSplit_witness_opposite_marker
      s (F i) (F j) hs
      (hLeaves i) (hLeaves j) hSi hSj rfl
  refine ⟨i, j, s, hi, hij, hHigh, hs, rfl, hSi, hSj, ?_⟩
  tauto

end DiaryLeafPriority
end ThreeUniformDiaries
