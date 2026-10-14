import Milliken.FiniteColourRamseySpace

/-!
# Generic finite-colouring adapters for the ATR Ramsey-space application

The finite-colouring lemma is abstract Ramsey-space mathematics, not
a homogeneous-tree theorem. Retain these small ATR-local aliases for
source compatibility; no fixed-alphabet strong-tree proofs are imported.
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
