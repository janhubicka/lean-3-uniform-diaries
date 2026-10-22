import ThreeUniformDiaries.DiaryFiniteAlternatingOuterMeets
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface

/-!
# Three leaves alternating at a one-split force a genuine two-split

The E2 alternating-three-leaf gadget cannot exist in a diary
with only 1-splits: among the three ordered leaf pairs (a,b),
(a,c), (b,c), their V3 marker-one bits have two distinct
orientations on the adjacent pairs. The third marker bit must
agree with one of the two. Those two pair types have full
meet at least 2 but STRICTLY below their first-leaf cap.
The S2 axiom therefore forces a genuine 2-split.

The outer singleton meet (a,c) is strictly later than the
adjacent split s, so S1 supplies a SECOND genuine 1-split.
Consequently every such gadget contains three leaves,
two distinct one-splits and a two-split, apart from the
three fixed markers. The existing nine-vertex target has
exactly this pattern.

This module proves the structural implication, NOT any
general flip absorber or a global minimality theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A triple with the fixed zero marker and a genuine leaf
as its middle vertex cannot have a diary-permitted edge. -/
theorem finite_leaf_middle_no_zero_edge
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRolePrediaryBlock H n)
    (u v : Nat) (hu : IsLeaf H u) :
    ¬ H.edge 0 u v := by
  intro he
  rcases D.permitted_edge 0 u v he with
      hMarker | hOne | hTwo | hDevlin | hNormal
  · have hu3 : 3 ≤ u := hu.1
    rcases hMarker.2.1 with hy1 | hy2 <;> omega
  · exact hu.2.1 hOne.2.1.2.1
  · have hh : 3 ≤ (0:Nat) := hTwo.1.1
    omega
  · rcases hDevlin.1 with hh | hh <;> omega
  · have hh : 3 ≤ (0:Nat) := hNormal.1.1
    omega

/-- If two genuine ordered leaf pairs have identical Devlin
marker-one bits, their complete 2-types agree through cut 2
provided both coordinate one-types agree there.
If the full meet is not its first-leaf cap, S2 makes that
meet a genuine two-split (it cannot equal marker 1). -/
theorem finite_same_marker_noncap_pairs_force_twoSplit
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hFirst : H.SameOneTypeBelow 2 a c)
    (hSecond : H.SameOneTypeBelow 2 b d)
    (hMarker : H.edge 1 a b ↔ H.edge 1 c d)
    (hNotCap : H.twoMeetLevel a b c d ≠ min a c) :
    IsTwoSplit H (H.twoMeetLevel a b c d) := by
  classical
  have hSame : H.SameTwoTypeBelow 2 a b c d := by
    refine ⟨hFirst,hSecond,?_⟩
    intro x hx2
    have hx : x = 0 ∨ x = 1 := by omega
    rcases hx with rfl | rfl
    · exact iff_of_false
        (finite_leaf_middle_no_zero_edge D.prediary a b ha)
        (finite_leaf_middle_no_zero_edge D.prediary c d hc)
    · exact hMarker
  have hTwoLower : 2 ≤ H.twoMeetLevel a b c d := by
    apply Nat.le_findGreatest
      (show 2 ≤ min a c by omega)
    exact hSame
  rcases D.pair_meets a b c d hab hcd hbn hdn
      ha hb hc hd with hCap | hOne | hSplit
  · exact False.elim (hNotCap hCap)
  · have hb : 2 ≤ (1:Nat) := by
      rw [hOne] at hTwoLower
      exact hTwoLower
    omega
  · exact hSplit

/-- Any alternating three-leaf 1-split witness forces
a genuine 2-split somewhere in the same finite diary.
The proof requires no extra split-control independence:
it is a direct pigeonhole argument using V3 and S2. -/
theorem finite_three_leaf_alternation_forces_twoSplit
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n)
    (s a b c : Nat)
    (hs : IsOneSplit H s)
    (hsa : s < a) (hab : a < b) (hbc : b < c)
    (hcn : c < n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c)
    (hAB : H.oneMeetLevel a b = s)
    (hBC : H.oneMeetLevel b c = s) :
    ∃ t : Nat, IsTwoSplit H t := by
  classical
  have hac : a < c := lt_trans hab hbc
  have hABMark : H.edge 1 a b ↔ H.edge 0 s b :=
    (D.prediary.leaf_marker_one a b hab (by omega) ha hb).trans
      (E_oneSplit_lexEarlier_iff_right
        D.prediary.permitted_edge
        s a b hs hab hsa hAB)
  have hBCMark : H.edge 1 b c ↔ H.edge 0 s c :=
    (D.prediary.leaf_marker_one b c hbc hcn hb hc).trans
      (E_oneSplit_lexEarlier_iff_right
        D.prediary.permitted_edge
        s b c hs hbc (by omega) hBC)
  have hDiff : ¬ (H.edge 0 s b ↔ H.edge 0 s c) :=
    E_oneSplit_distinguishing_zero_bit
      D.prediary.permitted_edge s b c hs hbc (by omega) hBC
  have hOpp : ¬ (H.edge 1 a b ↔ H.edge 1 b c) := by
    intro h
    exact hDiff (hABMark.symm.trans (h.trans hBCMark))
  have hABTwo : H.SameOneTypeBelow 2 a b := by
    intro x y hxy hy2
    have hh := H.oneMeetLevel_agree a b
    rw [hAB] at hh
    exact hh hxy (by omega)
  have hBCTwo : H.SameOneTypeBelow 2 b c := by
    intro x y hxy hy2
    have hh := H.oneMeetLevel_agree b c
    rw [hBC] at hh
    exact hh hxy (by omega)
  have hSelfTwo (u : Nat) : H.SameOneTypeBelow 2 u u := by
    intro x y hxy hy
    exact Iff.rfl
  by_cases hACAB : H.edge 1 a c ↔ H.edge 1 a b
  · have hNotCap : H.twoMeetLevel a b a c ≠ min a a := by
      have hUpper :
          H.twoMeetLevel a b a c ≤ H.oneMeetLevel b c := by
        rw [H.twoMeetLevel_eq_min a b a c hab hac]
        exact (min_le_right _ _).trans (min_le_right _ _)
      intro heq
      rw [hBC] at hUpper
      simp only [min_self] at heq
      omega
    have hSplit := finite_same_marker_noncap_pairs_force_twoSplit
      D a b a c hab hac (by omega) hcn ha hb ha hc
      (hSelfTwo a) hBCTwo hACAB.symm hNotCap
    exact ⟨H.twoMeetLevel a b a c,hSplit⟩
  · have hACBC : H.edge 1 a c ↔ H.edge 1 b c := by
      tauto
    have hNotCap : H.twoMeetLevel a c b c ≠ min a b := by
      have hUpper :
          H.twoMeetLevel a c b c ≤ H.oneMeetLevel a b := by
        rw [H.twoMeetLevel_eq_min a c b c hac hbc]
        exact (min_le_right _ _).trans (min_le_left _ _)
      intro heq
      rw [hAB] at hUpper
      simp only [min_eq_left hab.le] at heq
      omega
    have hSplit := finite_same_marker_noncap_pairs_force_twoSplit
      D a c b c hac hbc hcn hcn ha hc hb hc
      hABTwo (hSelfTwo c) hACBC hNotCap
    exact ⟨H.twoMeetLevel a c b c,hSplit⟩

/-- The same alternating triple also forces a second DISTINCT
1-split strictly later than the original split. -/
theorem finite_three_leaf_alternation_forces_later_oneSplit
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n)
    (s a b c : Nat)
    (hs : IsOneSplit H s)
    (hsa : s < a) (hab : a < b) (hbc : b < c)
    (hcn : c < n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c)
    (hAB : H.oneMeetLevel a b = s)
    (hBC : H.oneMeetLevel b c = s) :
    ∃ t : Nat, s < t ∧ IsOneSplit H t := by
  have hOuter := finite_three_leaf_outer_oneMeet_gt
    D.prediary s a b c hs hsa hab hbc hAB hBC
  refine ⟨H.oneMeetLevel a c,hOuter,?_⟩
  exact D.singleton_meets a c (lt_trans hab hbc)
    hcn ha hc

end DiaryLeafPriority
end ThreeUniformDiaries
