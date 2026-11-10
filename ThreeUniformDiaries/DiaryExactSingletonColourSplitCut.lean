import ThreeUniformDiaries.DiaryHighTwoSidedE2RangeWitness
import ThreeUniformDiaries.DiaryFiniteSingletonColour

/-!
# Track C: exact first divergence of complete singleton colours at S1 meets

English proof and independent adversarial review:
  janhubicka/3-uniform-diaries PR #273
  notes/track_c_exact_singleton_colour_threshold_20261110.md

For two DISTINCT genuine leaves of a full RoleDiary, their complete
finite singleton colours at cut B are EQUAL iff B is no greater than
their exact numeric one-meet. At the first excluded cut s+1, the
true one-split's opposite E2 branch bits force inequality.

Unlike the existing general oneMeet lower-bound criterion this iff
does NOT assume B ≤ a,b; it uses full diary S1, actual leaf roles and
a ≠ b. A high-pair corollary applies to any unordered injected leaf
range. No prescribed old support or persistent successor is realized.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Exact cutoff for equality of the full finite mixed singleton
colours of TWO DISTINCT GENUINE leaves in a RoleDiary:
colour equality at B iff B ≤ their one-meet, for EVERY B.

The converse genuinely uses the witnessed E2 opposite bits at
the one-split. It fails for arbitrary edgeless graphs and for a=b. -/
theorem RoleDiary.singletonColour_eq_iff_cut_le_oneMeet
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    {a b : Nat} (ha : IsLeaf K a) (hb : IsLeaf K b)
    (hNe : a ≠ b) (B : Nat) :
    DiaryLowerBoundColors.singletonColour K B a =
      DiaryLowerBoundColors.singletonColour K B b ↔
    B ≤ K.oneMeetLevel a b := by
  classical
  let s := K.oneMeetLevel a b
  have hsRole : IsOneSplit K s :=
    DK.singleton_meets a b ha hb hNe
  have hsCap : s ≤ min a b := K.oneMeetLevel_le_min a b
  have hsA : s < a := by
    have hne : s ≠ a := by
      intro h
      have hOne : IsOneSplit K a := by simpa only [h] using hsRole
      exact ha.2.1 hOne.2.1
    omega
  have hsB : s < b := by
    have hne : s ≠ b := by
      intro h
      have hOne : IsOneSplit K b := by simpa only [h] using hsRole
      exact hb.2.1 hOne.2.1
    omega
  have hsZero : 0 < s := by
    have hThree := hsRole.1
    omega
  have hOpp : ¬ (K.edge 0 s a ↔ K.edge 0 s b) :=
    DK.oneSplit_witness_opposite_marker
      s a b hsRole ha hb hsA hsB rfl
  constructor
  · intro hEq
    by_contra hNot
    have hBelow : s < B := by omega
    have hSame : K.SameOneTypeBelow B a b :=
      (DiaryLowerBoundColors.singletonColour_eq_iff K B a b).mp hEq
    exact hOpp (hSame 0 s hsZero hBelow)
  · intro hB
    apply (DiaryLowerBoundColors.singletonColour_eq_iff K B a b).mpr
    intro x y hxy hyB
    exact (K.oneMeetLevel_agree a b) hxy (by omega)

/-- The first finite mixed singleton-colour difference of any
distinct true leaves occurs EXACTLY when their genuine S1 meet
enters the cut. Equality holds at s; inequality at s+1. -/
theorem RoleDiary.singletonColour_first_difference_at_oneMeet
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    {a b : Nat} (ha : IsLeaf K a) (hb : IsLeaf K b)
    (hNe : a ≠ b) :
    (DiaryLowerBoundColors.singletonColour
        K (K.oneMeetLevel a b) a =
      DiaryLowerBoundColors.singletonColour
        K (K.oneMeetLevel a b) b) ∧
    (DiaryLowerBoundColors.singletonColour
        K (K.oneMeetLevel a b + 1) a ≠
      DiaryLowerBoundColors.singletonColour
        K (K.oneMeetLevel a b + 1) b) := by
  constructor
  · exact (DK.singletonColour_eq_iff_cut_le_oneMeet
      ha hb hNe (K.oneMeetLevel a b)).mpr (le_refl _)
  · intro hEq
    have hImpossible :=
      (DK.singletonColour_eq_iff_cut_le_oneMeet
        ha hb hNe (K.oneMeetLevel a b + 1)).mp hEq
    omega

/-- Every infinite injected range of true diary leaves contains
late pairs whose mixed singleton colours agree through ANY
prescribed finite cut B, but FIRST disagree at a larger
genuine one-split cut s+1.

The split s and witnesses are chosen together, not prescribed
by a previously fixed old diary support. -/
theorem RoleDiary.exists_late_first_singletonColour_split_in_leaf_range
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInj : Function.Injective F)
    (hLeaves : ∀ i : Nat, IsLeaf K (F i))
    (B N : Nat) :
    ∃ i j s : Nat,
      N ≤ i ∧ i < j ∧ B ≤ s ∧
      IsOneSplit K s ∧
      K.oneMeetLevel (F i) (F j) = s ∧
      (DiaryLowerBoundColors.singletonColour K B (F i) =
        DiaryLowerBoundColors.singletonColour K B (F j)) ∧
      (DiaryLowerBoundColors.singletonColour K (s + 1) (F i) ≠
        DiaryLowerBoundColors.singletonColour K (s + 1) (F j)) := by
  classical
  obtain ⟨i, j, s, hNi, hij, hBs, hsRole, hMeet,
      _hSi, _hSj, _hOpp⟩ :=
    DK.exists_high_two_sided_E2_split_in_leaf_range
      F hInj hLeaves B N
  have hNe : F i ≠ F j := by
    intro heq
    exact (ne_of_lt hij) (hInj heq)
  have hBound : B ≤ K.oneMeetLevel (F i) (F j) := by
    rw [hMeet]
    exact hBs
  refine ⟨i, j, s, hNi, hij, hBs, hsRole, hMeet, ?_, ?_⟩
  · exact (DK.singletonColour_eq_iff_cut_le_oneMeet
      (hLeaves i) (hLeaves j) hNe B).mpr hBound
  · intro hEq
    have hImpossible :=
      (DK.singletonColour_eq_iff_cut_le_oneMeet
        (hLeaves i) (hLeaves j) hNe (s + 1)).mp hEq
    rw [hMeet] at hImpossible
    omega

end DiaryLeafPriority
end ThreeUniformDiaries
