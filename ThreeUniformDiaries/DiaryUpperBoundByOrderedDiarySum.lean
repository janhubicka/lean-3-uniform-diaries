import ThreeUniformDiaries.DiarySumOverAllIncreasingPresentations
import ThreeUniformDiaries.DiarySharpUpperOnEmbeddings
import ThreeUniformDiaries.DiarySharpUnlabelledUnconditionalUpper

/-!
# Track C: sharp unconditional upper bounds in the diary-count convention

The verified finite source count is exactly the SUM of full finite
diary numbers over ALL increasing ordered presentations of the
underlying unordered hypergraph A. The labelled source count then
multiplies that sum by |Aut(A)| EXACTLY ONCE.

The already verified unconditional upper-bound theorems construct
actual unordered induced self-embeddings of arbitrary countably
universal U, both for a colouring of genuine labelled embeddings
and for a colouring of unlabelled copies (finite vertex sets).

This module rewrites their EXACT palette lengths in terms of the
explicit sum over all ordered presentations, making the exported
upper-bound API match the manuscript's intended corrected counting
convention without an auxiliary definition-level hypothesis.

There is no new Ramsey induction and NO lower-bound claim here.
The countable diary unavoidability required for exact big Ramsey
degree equality remains separate and open.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- The unconditional sharp upper bound for colourings of TRUE
labelled embeddings of A, with the palette expressed as the
sum of full finite diaries over ALL distinct increasing ordered
presentations of its underlying unordered hypergraph, multiplied
by |Aut(A)| once and only once. -/
theorem actualFiniteAuxRamsey_sharp_upper_on_embeddings_orderedDiarySum
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsInducedLabelledCopy A U v} → κ) :
    ∃ w : UnorderedEmbedding U U,
      ∃ palette : List κ,
        palette.length =
          (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) *
            Fintype.card
              (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        ∀ v : Fin a → Nat,
          ∀ hv : IsInducedLabelledCopy A U v,
            χ ⟨(fun i => w (v i)),
              isInducedLabelledCopy_map_unordered A w v hv⟩ ∈ palette := by
  obtain ⟨w, palette, hlength, hcolour⟩ :=
    actualFiniteAuxRamsey_sharp_upper_on_embeddings
      G U hUniversal A χ
  refine ⟨w, palette, ?_, hcolour⟩
  rw [unmarkedDiaryCount_eq_sum_allIncreasingPresentations A]
    at hlength
  exact hlength

/-- The corresponding unconditional upper bound for colourings
of UNLABELLED finite copies: the SAME sum of ordered diary counts,
but with NO factor |Aut(A)|. The colouring reads finite vertex
sets, not the full space of labelled embeddings. -/
theorem actualFiniteAuxRamsey_sharp_unlabelled_upper_orderedDiarySum
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Finset Nat → κ) :
    ∃ w : UnorderedEmbedding U U,
      ∃ palette : List κ,
        palette.length =
          ∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card
          ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A U v →
          χ ((Finset.univ : Finset (Fin a)).image
            (fun i => w (v i))) ∈ palette := by
  obtain ⟨w, palette, hlength, hcolour⟩ :=
    actualFiniteAuxRamsey_sharp_unlabelled_upper
      G U hUniversal A χ
  refine ⟨w, palette, ?_, hcolour⟩
  rw [unmarkedDiaryCount_eq_sum_allIncreasingPresentations A]
    at hlength
  exact hlength

end ATRFiniteDecoder
end ThreeUniformDiaries
