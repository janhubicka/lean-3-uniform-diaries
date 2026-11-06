import ThreeUniformDiaries.DiaryExactDegreeRelabelInvariance
import ThreeUniformDiaries.DiaryExactLabelledBigRamseyDegreeNoGeneric

/-!
# The standard labelled big Ramsey bound is independent of A's labels

The full diary-count invariance theorem proves that the sharp
natural number is unchanged when the finite EnumNode A is relabelled
by an unordered induced isomorphism. Combined with the exact
no-generic-parameter upper/lower theorem, this gives equivalence
of the LITERAL standard finite-colouring big Ramsey bound predicates.

Thus both the numerical answer and the quantification over every
finite colouring and unordered self-copy are independent of the
chosen source enumeration. This final wrapper uses the previously
checked upper/lower result but no countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Every labelled finite big Ramsey bound has the same truth value
for any two enumerations of the SAME unordered finite A. The target U
may be an arbitrary countably universal unordered 3-hypergraph. -/
theorem labelledBigRamseyBound_iff_of_unordered_relabelling
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A B : EnumNode a)
    (τ : Equiv.Perm (Fin a))
    (hIso : IsUnorderedRelabelling A B τ)
    (t : Nat) :
    IsLabelledBigRamseyBound U A t ↔
      IsLabelledBigRamseyBound U B t := by
  rw [labelledBigRamseyBound_iff_exactDiaryCount_le_noGeneric
        U hUniversal A t,
      labelledBigRamseyBound_iff_exactDiaryCount_le_noGeneric
        U hUniversal B t,
      exactOrderedDiaryDegree_eq_of_relabelling A B τ hIso]

end ATRFiniteDecoder
end ThreeUniformDiaries
