import ThreeUniformDiaries.ATRGeneralMilliken
import ThreeUniformDiaries.AuxRamseyTransfer

/-!
# Transfer fixed-stem scalar Milliken to the existing ATR Ramsey argument

General scalar finite approximations need not have the rooted shape of
an ATR vector code. Accordingly the finite decoder below returns an
Option. The colouring assigns an arbitrary default to invalid scalar
approximations and uses the ATR colouring on valid ones.

The substantive geometric input is the realization property:
every refined finite ATR code is the decoder image of some scalar
finite approximation in the selected strong tree, preserving its stem.

The general-tree Milliken property, the concrete rooted-tree model,
and this realization property are explicit inputs, never axioms.
-/

namespace ThreeUniformDiaries
namespace ATRGeneralMilliken

open Milliken

universe u₁ u₂ u₃ u₄ u₅

/-- The exact representation data required to apply an arbitrary-tree
scalar strong-subtree colouring to the finite ATR codes. -/
structure ATRScalarRealization
    {SmallEmb : Type u₁} {LargeEmb : Type u₂}
    {BranchEmb : Type u₃} {FinCode : Type u₄} {InfCode : Type u₅}
    (C : AuxRamseyCoding SmallEmb LargeEmb BranchEmb FinCode InfCode)
    (T : Milliken.AmbientTree) where
  stem : Nat
  height : Nat
  initial : Milliken.GeneralTree.StrongSubtree T
  decodeApprox :
    Milliken.GeneralTree.FiniteApprox T height → Option FinCode
  decodeInfinite :
    Milliken.GeneralTree.StrongSubtree T → InfCode
  realize :
    ∀ B : Milliken.GeneralTree.StrongSubtree T,
      B.Refines initial →
      Milliken.GeneralTree.r stem B =
        Milliken.GeneralTree.r stem initial →
      ∀ S : FinCode,
        ∃ X : Milliken.GeneralTree.StrongSubtree T,
          X.Refines B ∧
          Milliken.GeneralTree.r stem X =
            Milliken.GeneralTree.r stem initial ∧
          decodeApprox (Milliken.GeneralTree.r height X) =
            some (C.refine (decodeInfinite B) S)

namespace ATRScalarRealization

variable {SmallEmb : Type u₁} {LargeEmb : Type u₂}
  {BranchEmb : Type u₃} {FinCode : Type u₄} {InfCode : Type u₅}
  {C : AuxRamseyCoding SmallEmb LargeEmb BranchEmb FinCode InfCode}
  {T : Milliken.AmbientTree}

/-- The non-homogeneous fixed-stem Milliken theorem yields exactly
the checked finite-colour hypothesis of the ATR coding reduction. -/
theorem finiteRamsey_of_generalMilliken
    (G : ATRScalarRealization C T)
    (hTop : RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := Milliken.GeneralTree.generalApproximationSystem T)) :
    C.FiniteRamsey := by
  intro Color hFintype hNonempty χ
  classical
  let defaultColour : Color := Classical.choice hNonempty
  let col : Milliken.GeneralTree.FiniteApprox T G.height → Color :=
    fun a => match G.decodeApprox a with
      | none => defaultColour
      | some s => χ s
  obtain ⟨B, hBA, hStem, hhom⟩ :=
    anchoredFiniteColour_of_generalMilliken
      T hTop G.stem G.height G.initial col
  refine ⟨G.decodeInfinite B,
    col (Milliken.GeneralTree.r G.height B), ?_⟩
  intro S
  obtain ⟨X, hXB, hXstem, hcode⟩ :=
    G.realize B hBA hStem S
  have hh := hhom X B hXB
    (Milliken.GeneralTree.StrongSubtree.refines_refl B)
    hXstem hStem
  have hcolour : col (Milliken.GeneralTree.r G.height X) =
      χ (C.refine (G.decodeInfinite B) S) := by
    simp only [col, hcode]
  exact hcolour.symm.trans hh

/-- Actual ATR Ramsey conclusion, conditional on the explicitly
supplied scalar Milliken theorem and concrete geometric realization. -/
theorem atrRamsey_of_generalMilliken
    (G : ATRScalarRealization C T)
    (hTop : RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := Milliken.GeneralTree.generalApproximationSystem T))
    (Color : Type) [Fintype Color] [Nonempty Color]
    (χ : SmallEmb → Color) :
    ∃ f : LargeEmb, ∃ c : Color,
      ∀ e : SmallEmb, χ (C.act f e) = c := by
  exact C.auxRamsey_of_finiteRamsey
    (G.finiteRamsey_of_generalMilliken hTop) Color χ

/-- The general-tree A.4 and Tychonoff closedness remain explicit
hypotheses, not postulates in the imported library. -/
theorem atrRamsey_of_generalA4_closed
    (G : ATRScalarRealization C T)
    (hA4 : Milliken.GeneralTree.HasGeneralPigeonhole T)
    (hclosed :
      (Milliken.GeneralTree.generalApproximationSystem T).IsTychonoffClosed)
    (Color : Type) [Fintype Color] [Nonempty Color]
    (χ : SmallEmb → Color) :
    ∃ f : LargeEmb, ∃ c : Color,
      ∀ e : SmallEmb, χ (C.act f e) = c := by
  exact G.atrRamsey_of_generalMilliken
    (generalMilliken_of_A4_closed T hA4 hclosed) Color χ

end ATRScalarRealization
end ATRGeneralMilliken
end ThreeUniformDiaries
