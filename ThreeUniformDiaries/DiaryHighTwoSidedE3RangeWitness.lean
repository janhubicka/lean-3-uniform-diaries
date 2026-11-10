import ThreeUniformDiaries.DiaryHighTwoSidedE2RangeWitness
import ThreeUniformDiaries.DiaryTwoSplitWitnessClasses
import ThreeUniformDiaries.DiaryExactS2Cap
import ThreeUniformDiaries.DiaryFinitePairColour

/-!
# Track D: high two-sided E3 witnesses in every injected genuine-leaf range

The E2 result gives arbitrarily high genuine one-split witnesses of
both orientations in any injective leaf range. Here we prove the
corresponding TWO-SPLIT fact for E3 without assuming that the range is
ordered or induced generic.

Select cofinally many ordered leaf PAIRS from the prescribed range.
The full pair type below a finite cut has a finite colour (both
coordinate singleton masks and the auxiliary pair mask). Hence one
full pair colour recurs cofinally. Two separated pairs of this colour
have a full pair meet above the cut. S2 makes that meet a genuine
two-split: the capped alternative would identify the distinct first
leaves, and the marker-one alternative lies below the cut.
The actual split-witness law forces opposite E3 bits.

The split and both witness pairs are chosen together. This does NOT
realize an E3 value at a preassigned old-stage split, provide
simultaneous E2/E3 control, or build a relative countable extension.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At arbitrarily high target two-split levels, both E3 incidences
occur on two disjoint ordered pairs of leaves from the ORIGINAL
prescribed injected range. The outer enumeration F need not be
increasing, and neither the split nor the old support is prescribed. -/
theorem RoleDiary.exists_high_two_sided_E3_split_in_leaf_range
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat) (hInj : Function.Injective F)
    (hLeaves : ∀ i : Nat, IsLeaf K (F i))
    (B N : Nat) :
    ∃ i j k l s : Nat,
      N ≤ i ∧ i < j ∧ j < k ∧ k < l ∧
      F i < F j ∧ F k < F l ∧
      B ≤ s ∧ IsTwoSplit K s ∧
      K.twoMeetLevel (F i) (F j) (F k) (F l) = s ∧
      s < F i ∧ s < F k ∧
      ((K.edge s (F i) (F j) ∧ ¬ K.edge s (F k) (F l)) ∨
       (¬ K.edge s (F i) (F j) ∧ K.edge s (F k) (F l))) := by
  classical
  let T := max B 3
  have hPair (n : Nat) :
      ∃ i j : Nat,
        n ≤ i ∧ i < j ∧ T ≤ F i ∧ T ≤ F j ∧ F i < F j := by
    obtain ⟨M, hM⟩ := injective_nat_eventually_above_bound F hInj T
    let i := max n M
    obtain ⟨L, hL⟩ := injective_nat_eventually_above_bound F hInj (F i)
    let j := max (i + 1) L
    have hni : n ≤ i := by dsimp [i]; omega
    have hMi : M ≤ i := by dsimp [i]; omega
    have hij : i < j := by dsimp [j]; omega
    have hLj : L ≤ j := by dsimp [j]; omega
    have hTi : T < F i := hM i hMi
    have hFij : F i < F j := hL j hLj
    exact ⟨i, j, hni, hij, le_of_lt hTi, by omega, hFij⟩
  let first : Nat → Nat := fun n => Classical.choose (hPair n)
  let second : Nat → Nat :=
    fun n => Classical.choose (Classical.choose_spec (hPair n))
  have hSpec (n : Nat) :
      n ≤ first n ∧ first n < second n ∧
      T ≤ F (first n) ∧ T ≤ F (second n) ∧
      F (first n) < F (second n) := by
    exact Classical.choose_spec (Classical.choose_spec (hPair n))
  let C :=
    ((Fin T → Fin T → Bool) × (Fin T → Fin T → Bool)) ×
      ((Fin T → Bool) × Bool)
  let colour : Nat → C := fun n =>
    ((DiaryLowerBoundColors.singletonColour K T (F (first n)),
      DiaryLowerBoundColors.singletonColour K T (F (second n))),
      DiaryLowerBoundColors.pairColour K T
        (F (first n)) (F (second n)))
  let R : C → Nat → Prop := fun c N =>
    ∃ n : Nat, N ≤ n ∧ colour n = c
  have hDown : ∀ (c : C) (n k : Nat),
      k ≤ n → R c n → R c k := by
    intro c n k hkn
    rintro ⟨m, hnm, hColour⟩
    exact ⟨m, hkn.trans hnm, hColour⟩
  have hCover : ∀ N : Nat, ∃ c : C,
      c ∈ (Finset.univ : Finset C) ∧ R c N := by
    intro n
    exact ⟨colour n, Finset.mem_univ _, n, le_rfl, rfl⟩
  obtain ⟨c, _hc, hRec⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) R hDown hCover
  obtain ⟨n₀, hn₀, hc₀⟩ := hRec N
  obtain ⟨n₁, hn₁, hc₁⟩ := hRec (second n₀ + 1)
  obtain ⟨hni, hij, hTa, hTb, hab⟩ := hSpec n₀
  obtain ⟨hnk, hkl, hTc, hTd, hcd⟩ := hSpec n₁
  have hjk : second n₀ < first n₁ := by omega
  have hColour : colour n₀ = colour n₁ := hc₀.trans hc₁.symm
  have hFirst :
      DiaryLowerBoundColors.singletonColour K T (F (first n₀)) =
      DiaryLowerBoundColors.singletonColour K T (F (first n₁)) :=
    congrArg (fun z : C => z.1.1) hColour
  have hSecond :
      DiaryLowerBoundColors.singletonColour K T (F (second n₀)) =
      DiaryLowerBoundColors.singletonColour K T (F (second n₁)) :=
    congrArg (fun z : C => z.1.2) hColour
  have hPairColour :
      DiaryLowerBoundColors.pairColour K T
        (F (first n₀)) (F (second n₀)) =
      DiaryLowerBoundColors.pairColour K T
        (F (first n₁)) (F (second n₁)) :=
    congrArg (fun z : C => z.2) hColour
  have hSame :
      K.SameTwoTypeBelow T
        (F (first n₀)) (F (second n₀))
        (F (first n₁)) (F (second n₁)) :=
    ⟨(DiaryLowerBoundColors.singletonColour_eq_iff K T
        (F (first n₀)) (F (first n₁))).mp hFirst,
     (DiaryLowerBoundColors.singletonColour_eq_iff K T
        (F (second n₀)) (F (second n₁))).mp hSecond,
     ((DiaryLowerBoundColors.pairColour_eq_iff K T
        (F (first n₀)) (F (second n₀))
        (F (first n₁)) (F (second n₁))).mp hPairColour).1⟩
  have hMeetHigh :
      T ≤ K.twoMeetLevel
        (F (first n₀)) (F (second n₀))
        (F (first n₁)) (F (second n₁)) :=
    Nat.le_findGreatest (le_min hTa hTc) hSame
  have hFirstNe : F (first n₀) ≠ F (first n₁) := by
    intro h
    have hEq : first n₀ = first n₁ := hInj h
    omega
  have hTwo : IsTwoSplit K
      (K.twoMeetLevel
        (F (first n₀)) (F (second n₀))
        (F (first n₁)) (F (second n₁))) := by
    rcases DK.pair_meets
      (F (first n₀)) (F (second n₀))
      (F (first n₁)) (F (second n₁))
      hab hcd
      (hLeaves (first n₀)) (hLeaves (second n₀))
      (hLeaves (first n₁)) (hLeaves (second n₁)) with
      hCap | hOne | hSplit
    · have hEq := DK.capped_pair_first_components_equal
        (F (first n₀)) (F (second n₀))
        (F (first n₁)) (F (second n₁))
        hab hcd
        (hLeaves (first n₀)) (hLeaves (second n₀))
        (hLeaves (first n₁)) (hLeaves (second n₁))
        hCap
      exact False.elim (hFirstNe hEq)
    · have hT3 : 3 ≤ T := le_max_right B 3
      omega
    · exact hSplit
  let s := K.twoMeetLevel
    (F (first n₀)) (F (second n₀))
    (F (first n₁)) (F (second n₁))
  have hCapBound : s ≤ min (F (first n₀)) (F (first n₁)) :=
    K.twoMeetLevel_le_min
      (F (first n₀)) (F (second n₀))
      (F (first n₁)) (F (second n₁))
  have hNotA : s ≠ F (first n₀) := by
    intro h
    have hAtA : IsTwoSplit K (F (first n₀)) := h ▸ hTwo
    exact (hLeaves (first n₀)).2.2 hAtA.2.2
  have hNotC : s ≠ F (first n₁) := by
    intro h
    have hAtC : IsTwoSplit K (F (first n₁)) := h ▸ hTwo
    exact (hLeaves (first n₁)).2.2 hAtC.2.2
  have hsa : s < F (first n₀) := by
    have h := hCapBound.trans (min_le_left _ _)
    omega
  have hsc : s < F (first n₁) := by
    have h := hCapBound.trans (min_le_right _ _)
    omega
  have hOpp :
      ¬ (K.edge s (F (first n₀)) (F (second n₀)) ↔
         K.edge s (F (first n₁)) (F (second n₁))) :=
    DK.twoSplit_witness_opposite_incidence s
      (F (first n₀)) (F (second n₀))
      (F (first n₁)) (F (second n₁))
      hTwo hsa hsc rfl
  refine ⟨first n₀, second n₀, first n₁, second n₁, s,
    hn₀.trans hni, hij, hjk, hkl, hab, hcd,
    (le_max_left B 3).trans hMeetHigh, hTwo, rfl, hsa, hsc, ?_⟩
  tauto

end DiaryLeafPriority
end ThreeUniformDiaries
