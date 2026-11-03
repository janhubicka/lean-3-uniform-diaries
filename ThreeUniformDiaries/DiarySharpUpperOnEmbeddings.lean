import ThreeUniformDiaries.DiaryUpperBoundSharpUnconditional
import ThreeUniformDiaries.DiaryUpperBoundUnorderedCopyModelTransfer

/-!
# Track A: colour genuine embeddings rather than arbitrary labelled tuples

The circulation introduction defines big Ramsey degrees by colouring
Emb(A,U), not all maps Fin a → U. The already verified sharp labelled
upper theorem accepts a total colouring of every tuple, but restricts
its conclusion to induced A-copies.

Here we close that routine yet important interface gap: extend any
colouring of the subtype of ACTUAL induced finite A-embeddings to all
tuples with an arbitrary default colour, apply the unconditional sharp
upper theorem, and restrict back to genuine embeddings. Unordered
induced self-embeddings preserve the exact subtype predicate.

This adds no Ramsey or diary assumptions, no countable unavoidability,
and no new automorphism factor. The resulting bound remains the genuine
unmarked diary-source count times exactly |Aut(A)|.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- The upper palette in precisely the embedding-colouring formulation:
the colouring domain consists only of injective labelled induced
copies of A in U. This is the formal counterpart of Emb(A,U) for a
fixed finite EnumNode presentation of A and a Nat presentation of U. -/
theorem actualFiniteAuxRamsey_sharp_upper_on_embeddings
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsInducedLabelledCopy A U v} → κ) :
    ∃ w : UnorderedEmbedding U U,
      ∃ palette : List κ,
        palette.length =
          (allGenuineUnmarkedDiarySources A).card *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        ∀ v : Fin a → Nat,
          ∀ hv : IsInducedLabelledCopy A U v,
            χ ⟨(fun i => w (v i)),
              isInducedLabelledCopy_map_unordered A w v hv⟩ ∈ palette := by
  classical
  let totalColour : (Fin a → Nat) → κ :=
    fun v =>
      if h : IsInducedLabelledCopy A U v then
        χ ⟨v, h⟩
      else Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨w, palette, hlength, hbound⟩ :=
    actualFiniteAuxRamsey_sharp_upper
      G U hUniversal A totalColour
  refine ⟨w, palette, hlength, ?_⟩
  intro v hv
  have hw : IsInducedLabelledCopy A U
      (fun i => w (v i)) :=
    isInducedLabelledCopy_map_unordered A w v hv
  have h := hbound v hv
  simpa only [totalColour, dif_pos hw] using h

end ATRFiniteDecoder
end ThreeUniformDiaries
