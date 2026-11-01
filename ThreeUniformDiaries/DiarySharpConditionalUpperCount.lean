import ThreeUniformDiaries.DiaryMarkedUnmarkedGlobalCount
import ThreeUniformDiaries.DiaryUpperBoundUnorderedDirectTransfer

/-!
# Track C: exact conditional upper bound with the genuine diary count

The general direct ambient upper-bound transfer was proved earlier.
It produces a palette indexed by a finite list of marked actual
auxiliary-type-respecting source codes, PROVIDED every relevant
labelled copy factors through one of these genuine finite codes.

The cutoff-free list of *all* genuine marked diary sources of A is
already verified. Track C's finite cardinality theorem identifies
its length as the number of distinct underlying genuine unmarked
diary sources times the exact source automorphism cardinal.

This file only assembles those independent results. It does NOT
assume that a chosen generic-to-diary embedding or arbitrary
labelled A-copy already has the required source-code factorisation.
It does not identify the unmarked source cardinal with an
unspecified convention for "diaries of unordered A", and it
does not establish the separate lower bound.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Exact sharp *conditional* upper bound in terms of the actual
deduplicated finite family of unmarked genuine full diary sources.
No extra automorphism factor is inserted: the marked-source palette
already counts all complete-leaf markings, exactly once each. -/
theorem actualFiniteAuxRamsey_direct_upper_genuineDiaryCount
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (phi : UnorderedEmbedding K G.graph)
    (psi : UnorderedEmbedding G.graph K)
    (χ : (Fin a → Nat) → κ)
    (hFactors :
      ∀ v : Fin a → Nat,
        IsInducedLabelledCopy A K v →
        ∃ S ∈ allGenuineMarkedDiaryShapes A,
          ∃ e : S.source.Code G,
            ∀ i : Fin a, phi (v i) = e.image (S.marked i)) :
    ∃ w : UnorderedEmbedding K K,
      ∃ palette : List κ,
        palette.length =
          (allGenuineUnmarkedDiarySources A).card *
          Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A K v →
          χ (fun i => w (v i)) ∈ palette := by
  obtain ⟨w, palette, hlen, hcolour⟩ :=
    actualFiniteAuxRamsey_direct_upper_unordered_of_factorisation
      G K A phi psi χ (allGenuineMarkedDiaryShapes A) hFactors
  refine ⟨w, palette, ?_, hcolour⟩
  calc
    palette.length = (allGenuineMarkedDiaryShapes A).length :=
      hlen
    _ = allGenuineMarkedDiaryCount A := rfl
    _ = (allGenuineUnmarkedDiarySources A).card *
        Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a) :=
      allGenuineMarkedDiaryCount_eq_unmarked_mul_aut A

end ATRFiniteDecoder
end ThreeUniformDiaries
