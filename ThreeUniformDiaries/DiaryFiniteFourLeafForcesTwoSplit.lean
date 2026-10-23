import ThreeUniformDiaries.DiaryFiniteAlternatingRequiresTwoSplit
import ThreeUniformDiaries.DiaryFiniteGlobalDevlinOrientation

/-!
# Four ordered genuine leaves force a two-split

In every finite complete V/E/S diary, any four ordered genuine
leaves a<b<c<d force the existence of at least one genuine
2-split. This is a geometric S2 consequence, not a flip code
or a general finite absorber construction.

The three consecutive ordered leaf pairs (a,b),(b,c),(c,d)
have three Devlin marker-one bits, so two agree. Each chosen
pair of ordered pairs has DISTINCT first leaves. Their
numerical full pair meet is STRICTLY below the earlier first
leaf, since the singleton meet of distinct genuine leaves is
a genuine 1-split, never a leaf. Thus their pair-type meet
cannot be the first-leaf cap. Equality of the marker-one bits
ensures agreement through cut 2, ruling out marker 1. S2
forces a genuine 2-split.

The argument clarifies why 2-split geometry becomes unavoidable
as the leaf set grows. It does not prove that any proposed
independent E3 orientation bits are jointly realisable.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Two ordered leaf pairs with different first leaves and equal
marker-one bits necessarily have a full pair meet at a genuine
2-split. This does NOT require them to be disjoint: the pairs
(a,b) and (b,c), for example, are allowed. -/
theorem finite_distinct_first_leaf_pairs_same_marker_force_twoSplit
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d) (hac : a < c)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hMarker : H.edge 1 a b ↔ H.edge 1 c d) :
    IsTwoSplit H (H.twoMeetLevel a b c d) := by
  have hSplitAC : IsOneSplit H (H.oneMeetLevel a c) :=
    D.singleton_meets a c hac (by omega) ha hc
  have hMeetACLe : H.oneMeetLevel a c ≤ a :=
    (H.oneMeetLevel_le_min a c).trans (min_le_left _ _)
  have hMeetACNe : H.oneMeetLevel a c ≠ a := by
    intro hEq
    have hAone : IsOneSplit H a := by
      simpa only [hEq] using hSplitAC
    exact ha.2.1 hAone.2.1
  have hMeetAClt : H.oneMeetLevel a c < a := by omega
  have hUpper :
      H.twoMeetLevel a b c d ≤ H.oneMeetLevel a c := by
    rw [H.twoMeetLevel_eq_min a b c d hab hcd]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hNotCap : H.twoMeetLevel a b c d ≠ min a c := by
    rw [min_eq_left hac.le]
    omega
  exact finite_same_marker_noncap_pairs_force_twoSplit D
    a b c d hab hcd hbn hdn ha hb hc hd
    (finite_leaves_same_oneType_below_two ha hc)
    (finite_leaves_same_oneType_below_two hb hd)
    hMarker hNotCap

/-- Four increasing leaves have three consecutive ordered pairs
whose marker-one bits cannot all be pairwise unequal. Each
equality forces a genuine S2 two-split. -/
theorem finite_four_leaves_force_twoSplit
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n)
    (a b c d : Nat)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hdn : d < n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d) :
    ∃ s : Nat, IsTwoSplit H s := by
  by_cases hFirst : H.edge 1 a b ↔ H.edge 1 b c
  · exact ⟨H.twoMeetLevel a b b c,
      finite_distinct_first_leaf_pairs_same_marker_force_twoSplit
        D a b b c hab hbc hab
        (by omega) (by omega) ha hb hb hc hFirst⟩
  by_cases hSecond : H.edge 1 b c ↔ H.edge 1 c d
  · exact ⟨H.twoMeetLevel b c c d,
      finite_distinct_first_leaf_pairs_same_marker_force_twoSplit
        D b c c d hbc hcd hbc
        (by omega) hdn hb hc hc hd hSecond⟩
  have hOuter : H.edge 1 a b ↔ H.edge 1 c d := by
    tauto
  exact ⟨H.twoMeetLevel a b c d,
    finite_distinct_first_leaf_pairs_same_marker_force_twoSplit
      D a b c d hab hcd (by omega)
      (by omega) hdn ha hb hc hd hOuter⟩

/-- In the absence of any genuine 2-split, the finite diary
contains no strictly increasing four-leaf pattern. The
three-leaf bound is sharp as a combinatorial obstruction
only after a separate example is supplied; we make no
minimality claim here. -/
theorem finite_no_twoSplit_forbids_four_leaves
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n)
    (hNo : ∀ s : Nat, ¬ IsTwoSplit H s)
    (a b c d : Nat)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hdn : d < n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d) : False := by
  obtain ⟨s,hs⟩ :=
    finite_four_leaves_force_twoSplit
      D a b c d hab hbc hcd hdn ha hb hc hd
  exact hNo s hs

end DiaryLeafPriority
end ThreeUniformDiaries
