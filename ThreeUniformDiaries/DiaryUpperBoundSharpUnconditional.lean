import ThreeUniformDiaries.DiaryExistenceUnconditional
import ThreeUniformDiaries.DiaryUpperBoundSharpFromSeedLex

/-!
# Sharp big-Ramsey upper bound: discharge the final shifted-seed hypothesis

The terminal sharp upper-bound theorem had one remaining numerical
hypothesis: the true LexEarlier comparison of arbitrary U equals
that of the three-marker shifted seed. Track B proves this exactly,
including proper/capped meet cases, independently of all diary axioms.

This file applies that result to the ALREADY verified conditional
upper-bound theorem. It gives an unconditional upper bound for any
countably universal ordered 3-graph U. The bound is the number of
genuine unmarked diary sources of A times |Aut(A)|, with no second
automorphism factor. It does not claim the matching lower bound or
the exact big Ramsey degree.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Sharp genuine-diary-source palette upper bound with no
seed-V3, diary-leaf-model, source-cover, or countable unavoidability
hypothesis: the sole geometric premise is countable universality. -/
theorem actualFiniteAuxRamsey_sharp_upper
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : (Fin a → Nat) → κ) :
    ∃ w : UnorderedEmbedding U U,
      ∃ palette : List κ,
        palette.length =
          (allGenuineUnmarkedDiarySources A).card *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A U v →
          χ (fun i => w (v i)) ∈ palette := by
  exact actualFiniteAuxRamsey_sharp_upper_of_shiftedSeedLex
    G U hUniversal
    (fun a b hab => shiftedDiarySeed_lexEarlier_iff U a b hab)
    A χ

end ATRFiniteDecoder
end ThreeUniformDiaries
