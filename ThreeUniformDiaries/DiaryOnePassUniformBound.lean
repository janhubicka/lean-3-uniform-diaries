import ThreeUniformDiaries.DiaryOnePassFiniteSchedule

/-!
# Uniform finite-block bound for the concrete one-pass schedule

The manuscript's corrected completion proof requires a bound on the
number of inserted split vertices before ORIGINAL cut m that is
independent of the size/cardinality of the source pre-diary.

The actual schedule uses finitely many selected source singleton/full
pair germs in finite alphabets OneGermSpace m and TwoGermSpace m.
Even for a countably infinite input, the total number of events is
bounded by the sum of the two finite alphabet cardinalities.

This is a coarse but explicit fixed-cut bound; it does not rely on
the old moving-index termination argument or on S1/S2. More precise
closed-form bit-count bounds can be derived separately if useful.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The number of actual one-pass event vertices before original m
is uniformly bounded by finite type alphabets depending only on m,
for *every* ordered input hypergraph on Nat. -/
theorem onePassBlockSize_le_finiteGermAlphabet
    (H : Ordered3Graph Nat) (m : Nat) :
    onePassBlockSize H m ≤
      Fintype.card (TwoGermSpace m) +
      Fintype.card (OneGermSpace m) := by
  classical
  have hTwoBound : (selectedTwoGerms H m).card ≤
      Fintype.card (TwoGermSpace m) :=
    Finset.card_le_univ _
  have hOneBound : (selectedOneGerms H m).card ≤
      Fintype.card (OneGermSpace m) :=
    Finset.card_le_univ _
  by_cases hm : m < 3
  · simp [onePassBlockSize, onePassBlock, hm]
  · by_cases hTwo : IsTwoSplit H m
    · have hNotLeaf : ¬ IsLeaf H m := by
        intro hLeaf
        exact hLeaf.2.2 hTwo.2.2
      have hSize : onePassBlockSize H m = 0 := by
        simp [onePassBlockSize, onePassBlock, hm, hTwo, hNotLeaf]
      omega
    · by_cases hLeaf : IsLeaf H m
      · have hSize : onePassBlockSize H m =
            (selectedTwoGerms H m).card +
            (selectedOneGerms H m).card := by
          simp [onePassBlockSize, onePassBlock, hm, hTwo, hLeaf,
            sortOneGermsDescending_length]
        omega
      · have hSize : onePassBlockSize H m =
            (selectedTwoGerms H m).card := by
          simp [onePassBlockSize, onePassBlock, hm, hTwo, hLeaf]
        omega

/-- For any old prefix of length n, the TOTAL number of inserted
vertices before that old prefix ends is bounded independently of
the source by a finite sum of the same fixed-cut alphabets. -/
theorem onePassOldImage_le_uniformPrefixBound
    (H : Ordered3Graph Nat) (n : Nat) :
    onePassOldImage H n ≤
      n + (∑ i ∈ Finset.range (n + 1),
        (Fintype.card (TwoGermSpace i) +
         Fintype.card (OneGermSpace i))) := by
  have hsum : ∑ i ∈ Finset.range (n + 1), onePassBlockSize H i ≤
      ∑ i ∈ Finset.range (n + 1),
        (Fintype.card (TwoGermSpace i) +
         Fintype.card (OneGermSpace i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact onePassBlockSize_le_finiteGermAlphabet H i
  have heq : onePassOldImage H n =
      n + ∑ i ∈ Finset.range (n + 1),
        onePassBlockSize H i := by
    simp [onePassOldImage, onePassBefore, Finset.sum_range_succ]
    omega
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
