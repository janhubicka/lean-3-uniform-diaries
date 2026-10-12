import ThreeUniformDiaries.ATRScalarMillikenTransfer
import Milliken.GeneralTree.BoundaryMilliken

/-!
# Last Milliken application: eliminate the abstract A.4 and closure inputs

The general-tree library proves all of A.1--A.3 and Tychonoff closedness.
Moreover, genuine finite boundary-cone product Halpern--Läuchli implies A.4.
Here we put these checked theorems into the actual AuxRamseyCoding transfer.

There are exactly two remaining **concrete** obligations:
* `HasBoundaryProductHL U`: the still-unproved heterogeneous
  boundary-product Halpern--Läuchli input, without a global branching bound;
* `ATRScalarRealization C U`: the isomorphism/decoding between the
  actual three-coordinate vector pictures and scalar strong subtrees.

Neither is an axiom, instance, or hidden assumption. In particular
this is not yet an unconditional validation of manuscript Theorem ramsey.
-/

namespace ThreeUniformDiaries
namespace ATRGeneralMilliken

open Milliken

/-- The exact anchored finite-colouring consequence of genuine
heterogeneous boundary-product HL. Unlike the previous application,
A.4 and closedness are proved by the upstream library, rather than
passed as further independent assumptions. -/
theorem anchoredFiniteColour_of_boundaryProductHL
    (U : Milliken.AmbientTree)
    (hHL : Milliken.GeneralTree.HasBoundaryProductHL U)
    (n k : Nat) (A : Milliken.GeneralTree.StrongSubtree U)
    {κ : Type} [Fintype κ]
    (colour : Milliken.GeneralTree.FiniteApprox U k → κ) :
    ∃ B : Milliken.GeneralTree.StrongSubtree U,
      B.Refines A ∧
        Milliken.GeneralTree.r n B = Milliken.GeneralTree.r n A ∧
        ∀ X Y : Milliken.GeneralTree.StrongSubtree U,
          X.Refines B → Y.Refines B →
          Milliken.GeneralTree.r n X = Milliken.GeneralTree.r n A →
          Milliken.GeneralTree.r n Y = Milliken.GeneralTree.r n A →
          colour (Milliken.GeneralTree.r k X) =
            colour (Milliken.GeneralTree.r k Y) := by
  exact anchoredFiniteColour_of_A4_closed U
    (Milliken.GeneralTree.generalPigeonhole_of_boundaryProductHL U hHL)
    (Milliken.GeneralTree.generalIsTychonoffClosed U)
    n k A colour

namespace ATRScalarRealization

universe u₁ u₂ u₃ u₄ u₅

variable {SmallEmb : Type u₁} {LargeEmb : Type u₂}
  {BranchEmb : Type u₃} {FinCode : Type u₄} {InfCode : Type u₅}
  {C : AuxRamseyCoding SmallEmb LargeEmb BranchEmb FinCode InfCode}
  {U : Milliken.AmbientTree}

/-- The exact fixed-height ATR finite Ramsey property follows from
boundary-product HL and the concrete scalar/vector realization, with
no extra A.4, metric-closedness, or bounded-degree hypotheses. -/
theorem finiteRamsey_of_boundaryProductHL
    (G : ATRScalarRealization C U)
    (hHL : Milliken.GeneralTree.HasBoundaryProductHL U) :
    C.FiniteRamsey := by
  exact G.finiteRamsey_of_generalMilliken
    (generalMilliken_of_A4_closed U
      (Milliken.GeneralTree.generalPigeonhole_of_boundaryProductHL U hHL)
      (Milliken.GeneralTree.generalIsTychonoffClosed U))

/-- Final manuscript-shaped aux-type Ramsey consequence, with precisely
the two remaining mathematical inputs on its statement. -/
theorem atrRamsey_of_boundaryProductHL
    (G : ATRScalarRealization C U)
    (hHL : Milliken.GeneralTree.HasBoundaryProductHL U)
    (Color : Type) [Fintype Color] [Nonempty Color]
    (χ : SmallEmb → Color) :
    ∃ f : LargeEmb, ∃ c : Color,
      ∀ e : SmallEmb, χ (C.act f e) = c := by
  exact C.auxRamsey_of_finiteRamsey
    (G.finiteRamsey_of_boundaryProductHL hHL) Color χ

end ATRScalarRealization
end ATRGeneralMilliken
end ThreeUniformDiaries
