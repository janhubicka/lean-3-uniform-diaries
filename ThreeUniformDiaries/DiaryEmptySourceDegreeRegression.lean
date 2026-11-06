import ThreeUniformDiaries.DiaryExactUnlabelledCopySubtypeDegree
import ThreeUniformDiaries.DiaryConcreteCountablyUniversalWitness

/-!
# Track C regression: the empty finite hypergraph has degree one

An unordered finite copy of the empty hypergraph is the empty vertex
set, independently of the ambient hypergraph or its enumeration.
We first prove its unlabelled finite-colouring bound 1 directly,
without invoking any diary-counting or Ramsey theorem.

For countably universal U the degree cannot be 0: the copy domain
is inhabited, so a constant Unit colouring has a genuine colour.
Applying the fully verified exact unlabelled degree theorem to
the concrete countably universal pair-coded hypergraph then proves
that the sum over ALL increasing presentations of the empty source
has exactly one genuine unmarked full diary.

This is a genuine boundary regression of the numerical formula,
rather than a circular use of the formula to prove a bound.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

/-- An arbitrary ambient unordered hypergraph is an induced selfcopy
of itself. This explicit identity is useful for degenerate colours. -/
def unorderedEmbeddingId (U : Ordered3Graph Nat) :
    UnorderedEmbedding U U where
  toFun := id
  injective := by
    intro a b h
    exact h
  edge_iff := by
    intro a b c _ _
    exact Iff.rfl

/-- Every finite colouring of actual EMPTY vertex-set copies has at
most one colour in the entire ambient graph, with no universality or
Ramsey assumption. -/
theorem emptySource_unlabelledBigRamseyBound_one
    (U : Ordered3Graph Nat) (A : EnumNode 0) :
    IsUnlabelledBigRamseyBound U A 1 := by
  classical
  intro κ _ _ χ
  refine ⟨unorderedEmbeddingId U, {χ ∅}, by simp, ?_⟩
  intro v
  simp

/-- In a countably universal U, even the empty source has a
genuine induced copy; a constant Unit colouring excludes degree 0.
This proves positivity without using the diary counting formula. -/
theorem emptySource_not_unlabelledBigRamseyBound_zero
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (A : EnumNode 0) :
    ¬ IsUnlabelledBigRamseyBound U A 0 := by
  intro hBound
  obtain ⟨v⟩ := nonempty_genuineFiniteEmbeddings_of_universal
    U hUniversal A
  obtain ⟨w,palette,hCard,hCover⟩ :=
    hBound Unit (fun _ => ())
  have hCardZero : palette.card = 0 := by omega
  have hEmpty : palette = ∅ :=
    Finset.card_eq_zero.mp hCardZero
  have hMem := hCover v
  simp [hEmpty] at hMem

/-- Independent numerical regression: the complete unmarked
diary sum for the EMPTY unordered source is literally one. The
proof uses a direct one-colour argument and the already certified
exact-degree equivalence to rule out incorrect normalizations. -/
theorem emptySource_allIncreasingDiarySum_eq_one
    (A : EnumNode 0) :
    (∑ P ∈ allIncreasingPresentations A,
      (unmarkedDiariesOfIncreasingPresentation A P).card) = 1 := by
  let U := canonicalGenericEnumerated3Graph.graph
  have hOne : IsUnlabelledBigRamseyBound U A 1 :=
    emptySource_unlabelledBigRamseyBound_one U A
  have hLe :
      (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) ≤ 1 :=
    (unlabelledBigRamseyBound_iff_exactDiaryCount_le
      U canonicalGeneric_countablyUniversal A 1).mp hOne
  have hNonzero :
      (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) ≠ 0 := by
    intro hZero
    have hBoundZero : IsUnlabelledBigRamseyBound U A 0 :=
      (unlabelledBigRamseyBound_iff_exactDiaryCount_le
        U canonicalGeneric_countablyUniversal A 0).mpr (by omega)
    exact (emptySource_not_unlabelledBigRamseyBound_zero
      U canonicalGeneric_countablyUniversal A) hBoundZero
  omega

end ATRFiniteDecoder
end ThreeUniformDiaries
