import ThreeUniformDiaries.DiaryEmptySourceDegreeRegression
import ThreeUniformDiaries.DiaryExactLabelledBigRamseyDegreeNoGeneric

/-!
# Track C: independent empty-source LABELLED degree regression

The unlabelled empty-source degree and unmarked diary sum were checked
in the preceding module. Labelled induced embeddings of the empty
source are also unique as genuine subtype elements, not just up to
source automorphisms. Thus their finite-colouring degree is exactly
one, independently of any diary-counting or Ramsey result.

The verified exact labelled degree formula then forces the actual
empty-source automorphism count and complete MARKED diary count
to be one. This tests the difference between marked and unmarked
palettes at a=0, without assuming the factor to be one in advance.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

/-- Two actual labelled embeddings of the EMPTY finite source
are literally equal: their maps have domain Fin 0. -/
theorem emptySource_genuineEmbedding_subsingleton
    (U : Ordered3Graph Nat) (A : EnumNode 0)
    (v w : GenuineFiniteEmbeddings A U) :
    v = w := by
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

/-- The direct one-colour upper bound for labelled empty
embeddings; no diary, genericity or countable fusion is used.
Countable universality is only used to select a concrete copy. -/
theorem emptySource_labelledBigRamseyBound_one
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (A : EnumNode 0) :
    IsLabelledBigRamseyBound U A 1 := by
  classical
  let v₀ : GenuineFiniteEmbeddings A U :=
    Classical.choice
      (nonempty_genuineFiniteEmbeddings_of_universal
        U hUniversal A)
  intro κ _ _ χ
  refine ⟨unorderedEmbeddingId U, {χ v₀}, by simp, ?_⟩
  intro v
  have hv :
      v.postcompose (unorderedEmbeddingId U) = v₀ :=
    emptySource_genuineEmbedding_subsingleton U A _ _
  simp only [hv, Finset.mem_singleton_self]

/-- No zero-colour palette can cover a labelled empty A-copy:
there is always one actual embedding in countably universal U. -/
theorem emptySource_not_labelledBigRamseyBound_zero
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (A : EnumNode 0) :
    ¬ IsLabelledBigRamseyBound U A 0 := by
  intro hBound
  obtain ⟨v⟩ :=
    nonempty_genuineFiniteEmbeddings_of_universal U hUniversal A
  obtain ⟨w, palette, hCard, hCover⟩ :=
    hBound Unit (fun _ => ())
  have hCardZero : palette.card = 0 := by omega
  have hEmpty : palette = ∅ :=
    Finset.card_eq_zero.mp hCardZero
  have hMem := hCover v
  simp [hEmpty] at hMem

/-- Independent boundary regression: with NO source vertices,
the actual finite hypergraph automorphism group has exactly
one element. The proof checks consistency of the sharp labelled
formula against a direct one-colour argument and the independently
validated unmarked empty diary sum. -/
theorem emptySource_finiteHypergraphAut_card_eq_one
    (A : EnumNode 0) :
    Fintype.card (FiniteHypergraphAut A.toOrdered3Graph 0) = 1 := by
  let U := canonicalGenericEnumerated3Graph.graph
  let N : Nat :=
    (∑ P ∈ allIncreasingPresentations A,
       (unmarkedDiariesOfIncreasingPresentation A P).card) *
      Fintype.card (FiniteHypergraphAut A.toOrdered3Graph 0)
  have hOne : IsLabelledBigRamseyBound U A 1 :=
    emptySource_labelledBigRamseyBound_one
      U canonicalGeneric_countablyUniversal A
  have hLe : N ≤ 1 :=
    (labelledBigRamseyBound_iff_exactDiaryCount_le_noGeneric
      U canonicalGeneric_countablyUniversal A 1).mp hOne
  have hNoZero : ¬ IsLabelledBigRamseyBound U A 0 :=
    emptySource_not_labelledBigRamseyBound_zero
      U canonicalGeneric_countablyUniversal A
  have hNeZero : N ≠ 0 := by
    intro hN
    apply hNoZero
    exact (labelledBigRamseyBound_iff_exactDiaryCount_le_noGeneric
      U canonicalGeneric_countablyUniversal A 0).mpr (by omega)
  have hN : N = 1 := by omega
  dsimp [N] at hN
  rw [emptySource_allIncreasingDiarySum_eq_one A] at hN
  simpa only [one_mul] using hN

/-- The complete finite MARKED full-diary palette for the
empty source has cardinal one, exactly as the unmarked
palette. This catches any extraneous Aut(A) multiplier. -/
theorem emptySource_markedDiaryCount_eq_one
    (A : EnumNode 0) :
    allGenuineMarkedDiaryCount A = 1 := by
  rw [markedDiaryCount_eq_orderedDiarySum_mul_aut A,
      emptySource_allIncreasingDiarySum_eq_one A,
      emptySource_finiteHypergraphAut_card_eq_one A]
  norm_num

end ATRFiniteDecoder
end ThreeUniformDiaries
