import ThreeUniformDiaries.DiaryExactLabelledBigRamseyDegree
import ThreeUniformDiaries.DiaryGenericExistenceByPairCode

/-!
# Track C: the exact labelled big Ramsey degree, without a generic parameter

The numerical upper/lower equivalence is Lean-verified in the
preceding module. The explicit pair-pattern construction of an
enumerated generic 3-hypergraph is now independently merged and
Lean-verified. Instantiating the earlier theorem with that concrete
G eliminates its final artificial existence input.

The statement quantifies over arbitrary countably universal
3-uniform hypergraphs U and arbitrary finite enumerated 3-graphs A,
with the standard finite-colouring big Ramsey bound on ACTUAL
labelled induced embeddings. A self-copy of U need only be an
unordered induced embedding, as in the manuscript. All increasing
ordered presentations of the unordered A are counted, and the
automorphism group factor appears exactly once.

The stronger countable-source diary-unavoidability and countable
diary Ramsey theorems remain separate; they are not assumptions
of this numerical exact-degree theorem. No manuscript prose is
changed here.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

/-- Exact labelled big Ramsey degree formula, with NO supplied
enumerated generic hypergraph, diary, finite colouring, or
unavoidability hypothesis. The numerical predicate is the standard
quantification over finite colourings of actual labelled induced
A-embeddings and induced unordered U-selfcopies. -/
theorem labelledBigRamseyBound_iff_exactDiaryCount_le_noGeneric
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    (t : Nat) :
    IsLabelledBigRamseyBound U A t ↔
      (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) ≤ t :=
  labelledBigRamseyBound_iff_exactDiaryCount_le
    canonicalGenericEnumerated3Graph U hUniversal A t

/-- The diary formula is itself a valid labelled big Ramsey
bound, and EVERY other valid bound is at least as large. -/
theorem exactDiaryCount_is_unique_minimal_labelledBigRamseyBound
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a) :
    ∃! t : Nat,
      IsLabelledBigRamseyBound U A t ∧
      (∀ s : Nat, IsLabelledBigRamseyBound U A s → t ≤ s) := by
  let N : Nat :=
    (∑ P ∈ allIncreasingPresentations A,
      (unmarkedDiariesOfIncreasingPresentation A P).card) *
      Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a)
  have hN : IsLabelledBigRamseyBound U A N :=
    (labelledBigRamseyBound_iff_exactDiaryCount_le_noGeneric
      U hUniversal A N).mpr (Nat.le_refl N)
  refine ⟨N, ⟨hN, ?_⟩, ?_⟩
  · intro s hBound
    exact (labelledBigRamseyBound_iff_exactDiaryCount_le_noGeneric
      U hUniversal A s).mp hBound
  · intro s hs
    apply Nat.le_antisymm
    · exact hs.2 N hN
    · exact (labelledBigRamseyBound_iff_exactDiaryCount_le_noGeneric
        U hUniversal A s).mp hs.1

end ATRFiniteDecoder
end ThreeUniformDiaries
