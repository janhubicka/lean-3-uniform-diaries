import Milliken.GeneralTree.CanonicalPigeonhole
import Milliken.GeneralTree.PigeonholeInterface
import RamseySpace.AbstractEllentuck
import ThreeUniformDiaries.MillikenFiniteColour
import ThreeUniformDiaries.MillikenDependency

/-!
# The non-uniformly branching Milliken theorem: ATR-facing interface

The updated lean-milliken development has checked arbitrary rooted
locally finitely branching strong-tree geometry, approximation axioms
A.1–A.3, and the *conditional* construction of the general
Ramsey-space instance from A.4.

This module connects those exact checked interfaces to the fixed-stem
finite-colouring theorem required in the three-uniform ATR proof.
It records the two remaining logical inputs explicitly:

* arbitrary-tree A.4 (or its proved implication from canonical A.4);
* Tychonoff closedness of the general-tree approximation system.

Neither is silently assumed as a global instance or axiom.
The further root-gluing carrier/strong-tree transport from the
three concrete ATR coordinate trees is handled separately.
-/

namespace ThreeUniformDiaries
namespace ATRGeneralMilliken

open Milliken

/-- Arbitrary-tree A.1–A.4 from the exact general-tree A.4 property. -/
noncomputable def generalRamseySpace
    (U : Milliken.AmbientTree)
    (hA4 : Milliken.GeneralTree.HasGeneralPigeonhole U) :
    RamseySpace.AbstractRamseySpace
      (Milliken.GeneralTree.generalApproximationSystem U) :=
  Milliken.GeneralTree.abstractRamseySpace_of_pigeonhole U hA4

/-- The canonical-stem (Halpern–Läuchli) form of A.4 suffices
for the published full A.4 quantification in the ATR application. -/
theorem generalA4_of_canonical
    (U : Milliken.AmbientTree)
    (hCanonical : Milliken.GeneralTree.HasCanonicalPigeonhole U) :
    Milliken.GeneralTree.HasGeneralPigeonhole U :=
  Milliken.GeneralTree.generalPigeonhole_of_canonical U hCanonical

/-- Once the two remaining general-tree inputs are supplied,
the published Abstract Ellentuck theorem gives the literal
fixed-basic-neighbourhood Milliken conclusion. -/
theorem generalMilliken_of_A4_closed
    (U : Milliken.AmbientTree)
    (hA4 : Milliken.GeneralTree.HasGeneralPigeonhole U)
    (hclosed :
      (Milliken.GeneralTree.generalApproximationSystem U).IsTychonoffClosed) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := Milliken.GeneralTree.generalApproximationSystem U) := by
  exact RamseySpace.abstractEllentuck_textbook
    (generalRamseySpace U hA4) hclosed

/-- Fixed-stem finite colouring on any *non-homogeneous* finitely
branching rooted ambient U. This is the exact scalar conclusion
needed after the root-gluing of the three ATR coordinate trees.

This theorem is conditional on the explicitly supplied general-tree
topological Ramsey property; no fixed finite alphabet is selected. -/
theorem anchoredFiniteColour_of_generalMilliken
    (U : Milliken.AmbientTree)
    (hTop : RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := Milliken.GeneralTree.generalApproximationSystem U))
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
  let S := Milliken.GeneralTree.generalApproximationSystem U
  let a := Milliken.GeneralTree.r n A
  have hne : (S.neighborhood a A).Nonempty := by
    refine ⟨A, ?_⟩
    exact ⟨Milliken.GeneralTree.StrongSubtree.refines_refl A, rfl⟩
  obtain ⟨B, hBA, hhom⟩ :=
    RamseySpace.finiteApproximationColouring
      hTop a A hne colour
  refine ⟨B, hBA.1, hBA.2, ?_⟩
  intro X Y hXB hYB hX hY
  exact hhom X ⟨hXB, hX⟩ Y ⟨hYB, hY⟩

/-- The general-tree A.4 plus closedness delivers the actual scalar
finite-colour statement, with a protected first n selected levels. -/
theorem anchoredFiniteColour_of_A4_closed
    (U : Milliken.AmbientTree)
    (hA4 : Milliken.GeneralTree.HasGeneralPigeonhole U)
    (hclosed :
      (Milliken.GeneralTree.generalApproximationSystem U).IsTychonoffClosed)
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
  exact anchoredFiniteColour_of_generalMilliken
    U (generalMilliken_of_A4_closed U hA4 hclosed)
    n k A colour

end ATRGeneralMilliken
end ThreeUniformDiaries
