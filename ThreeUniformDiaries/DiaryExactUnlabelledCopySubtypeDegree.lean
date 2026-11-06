import ThreeUniformDiaries.DiaryUnlabelledCopyDomainEquivalence

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

/-- Exact unlabelled big Ramsey degree in the formulation where
a finite colouring is defined ONLY on actual induced copies of A,
rather than on all finite subsets of Nat. -/
theorem unlabelledBoundOnCopies_iff_exactDiaryCount_le
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) (t : Nat) :
    IsUnlabelledBigRamseyBoundOnCopies U A t ↔
      (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) ≤ t :=
  (isUnlabelledBigRamseyBound_iff_onActualCopies U A t).symm.trans
    (unlabelledBigRamseyBound_iff_exactDiaryCount_le
      U hUniversal A t)

/-- The genuine-copy-colouring formulation has the same unique
minimal integer degree: all increasing unordered-A presentations
are counted, without any automorphism multiplier. -/
theorem exactUnmarkedDiaryCount_unique_minimal_onActualCopies
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) :
    ∃! t : Nat,
      IsUnlabelledBigRamseyBoundOnCopies U A t ∧
      ∀ s : Nat, IsUnlabelledBigRamseyBoundOnCopies U A s →
        t ≤ s := by
  let N : Nat :=
    ∑ P ∈ allIncreasingPresentations A,
      (unmarkedDiariesOfIncreasingPresentation A P).card
  have hN : IsUnlabelledBigRamseyBoundOnCopies U A N :=
    (unlabelledBoundOnCopies_iff_exactDiaryCount_le
      U hUniversal A N).mpr (Nat.le_refl N)
  refine ⟨N, ⟨hN, ?_⟩, ?_⟩
  · intro s hs
    exact (unlabelledBoundOnCopies_iff_exactDiaryCount_le
      U hUniversal A s).mp hs
  · intro s hs
    apply Nat.le_antisymm
    · exact hs.2 N hN
    · exact (unlabelledBoundOnCopies_iff_exactDiaryCount_le
        U hUniversal A s).mp hs.1

end ATRFiniteDecoder
end ThreeUniformDiaries
