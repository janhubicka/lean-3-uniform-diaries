import Milliken.Applications

/-!
# Application of the standalone Milliken library

The generic finite-approximation colouring lemma and the homogeneous
finite-colour theorem now come from `lean-milliken`. Local aliases retain
the earlier 3-uniform API and provide a genuine downstream compile test.

This does not prove the manuscript's variable-branching synchronized
three-coordinate *vector* Milliken theorem; that transport is separate.
-/

namespace RamseySpace

universe u v w

namespace ApproximationSystem

variable {S : ApproximationSystem.{u, v}}

/-- Compatibility alias for the generic Ellentuck-open colour-fibre lemma. -/
theorem isOpen_approxColourClass
    {κ : Type w} (m : Nat) (colour : S.Approx m → κ) (c : κ) :
    @IsOpen S.Point S.ellentuckTopology
      {X | colour (S.approx m X) = c} :=
  isOpen_approxColourFibre_for_Milliken m colour c

end ApproximationSystem

/-- Compatibility alias for the generic finite-colouring theorem. -/
theorem finiteApproximationColouring
    {S : ApproximationSystem.{u, v}}
    (hTR : IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S))
    {κ : Type w} [Fintype κ]
    {n m : Nat} (a : S.Approx n) (A : S.Point)
    (hne : (S.neighborhood a A).Nonempty)
    (colour : S.Approx m → κ) :
    ∃ B, B ∈ S.neighborhood a A ∧
      ∀ X, X ∈ S.neighborhood a B →
        ∀ Y, Y ∈ S.neighborhood a B →
          colour (S.approx m X) = colour (S.approx m Y) :=
  finiteApproximationColouring_for_Milliken hTR a A hne colour

end RamseySpace

namespace ThreeUniformDiaries

open Milliken
universe u v

/-- The checked homogeneous finite-colour theorem, re-exported from the
standalone `lean-milliken` application API. -/
theorem homogeneousMillikenFiniteColouring
    {ι : Type u} [Finite ι] [Nonempty ι]
    {κ : Type v} [Fintype κ]
    (m : Nat)
    (colour : StrongTreeSpace.Approx ι m → κ) :
    ∃ B : StrongEmbedding ι,
      ∀ X Y : StrongEmbedding ι,
        StrongTreeSpace.le ι X B →
        StrongTreeSpace.le ι Y B →
        colour (StrongTreeSpace.approx ι m X) =
          colour (StrongTreeSpace.approx ι m Y) :=
  Milliken.Applications.millikenFiniteColouring m colour

end ThreeUniformDiaries
