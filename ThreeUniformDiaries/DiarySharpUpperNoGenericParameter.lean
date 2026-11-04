import ThreeUniformDiaries.DiaryGenericExistenceByPairCode
import ThreeUniformDiaries.DiaryUpperBoundByOrderedDiarySum

/-!
# Track A: sharp upper theorem without an assumed generic G parameter

The previously verified noncircular upper-bound endpoints took an
explicit G : GenericEnumerated3Graph argument. The manuscript simply
chooses an enumerated generic 3-hypergraph, so the formal statements
were conditional on a separate generic existence result.

The explicit finite-pair-pattern coding construction in
DiaryGenericExistenceByPairCode supplies a canonical actual G on Nat.
Instantiate the already verified theorems, retaining the exact
all-increasing-ordered-presentations count from Track C. Thus the
only structural input is the countable universality of U.

This is the unconditional (ordinary UNORDERED induced self-copy)
big-Ramsey upper bound for genuine labelled embeddings and finite
unlabelled copies. It still does not assert matching lower degree,
countable diary unavoidability, or the stronger diary-self-embedding
conclusion of the malformed printed upper theorem.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Exact sharp EMBEDDING-colouring upper bound for any countably
universal 3-graph U, with NO generic-structure parameter or
additional existence assumption, in the sum over all increasing
presentations of the unordered finite hypergraph A. -/
theorem actualFiniteAuxRamsey_sharp_upper_on_embeddings_noGeneric
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
  exact actualFiniteAuxRamsey_sharp_upper_on_embeddings_orderedDiarySum
    canonicalGenericEnumerated3Graph U hUniversal A χ

/-- For UNLABELLED A-copies the upper palette is the identical
full ordered-diary sum WITHOUT an automorphism factor. -/
theorem actualFiniteAuxRamsey_sharp_unlabelled_upper_noGeneric
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Finset Nat → κ) :
    ∃ w : UnorderedEmbedding U U,
      ∃ palette : List κ,
        palette.length =
          (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A U v →
          χ ((Finset.univ : Finset (Fin a)).image
            (fun i => w (v i))) ∈ palette := by
  exact actualFiniteAuxRamsey_sharp_unlabelled_upper_orderedDiarySum
    canonicalGenericEnumerated3Graph U hUniversal A χ

end ATRFiniteDecoder
end ThreeUniformDiaries
