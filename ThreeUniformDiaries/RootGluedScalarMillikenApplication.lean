import ThreeUniformDiaries.AuxRamseyTransfer
import ThreeUniformDiaries.MillikenDependency

/-!
# Explicit application of scalar fixed-stem Milliken to the ATR colouring

This closes the logical deduction from the exact scalar Milliken
finite-colour conclusion and the root-gluing refinement correspondence
to the auxiliary-type-respecting Ramsey theorem.

The scalar strong subtrees carry the extra common root and are meant
to encode the three genuine non-homogeneous type-tree coordinates.
Their type and the maps below are generic only because the
root-gluing strong-subtree equivalence is being verified separately.

Crucially, the available lean-milliken theorem is homogeneous and
therefore does NOT furnish the scalar non-homogeneous hypothesis
needed here. This file introduces NO axiom; hScalarMilliken remains
an explicit theorem hypothesis.
-/

namespace ThreeUniformDiaries

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇

/-- Exact refinement-compatibility interface of the root-gluing
correspondence between scalar strong subtrees and genuine vector
strong subtrees used by AuxRamseyCoding. This is the precise lemma
still to be instantiated by the concrete root-gluing construction. -/
structure RootGluedMillikenTransfer
    {SmallEmb : Type u₁} {LargeEmb : Type u₂}
    {BranchEmb : Type u₃} {FinCode : Type u₄}
    {InfCode : Type u₅}
    (C : AuxRamseyCoding SmallEmb LargeEmb BranchEmb FinCode InfCode)
    (ScalarFin : Type u₆) (ScalarInf : Type u₇) where
  glueFinite : FinCode → ScalarFin
  decodeFinite : ScalarFin → FinCode
  decodeInfinite : ScalarInf → InfCode
  scalarRefine : ScalarInf → ScalarFin → ScalarFin
  refinement :
    ∀ U : ScalarInf, ∀ S : FinCode,
      decodeFinite (scalarRefine U (glueFinite S)) =
        C.refine (decodeInfinite U) S

namespace RootGluedMillikenTransfer

variable {SmallEmb : Type u₁} {LargeEmb : Type u₂}
variable {BranchEmb : Type u₃} {FinCode : Type u₄}
variable {InfCode : Type u₅}
variable {ScalarFin : Type u₆} {ScalarInf : Type u₇}
variable {C : AuxRamseyCoding SmallEmb LargeEmb BranchEmb FinCode InfCode}

/-- Scalar fixed-stem Milliken in exactly the finite-colour form
required by the manuscript, with scalar refinement interpreted
inside the chosen infinite scalar strong witness. -/
def ScalarFiniteRamsey
    (T : RootGluedMillikenTransfer C ScalarFin ScalarInf) : Prop :=
  ∀ (Color : Type) [Fintype Color] [Nonempty Color]
      (c : ScalarFin → Color),
    ∃ U : ScalarInf, ∃ color : Color,
      ∀ S : ScalarFin, c (T.scalarRefine U S) = color

/-- Applying the scalar Milliken theorem after root-gluing gives
exactly the vector finite-code colouring conclusion needed
by the already verified ATR deduction. -/
theorem vectorFiniteRamsey_of_scalarMilliken
    (T : RootGluedMillikenTransfer C ScalarFin ScalarInf)
    (hScalarMilliken : T.ScalarFiniteRamsey) :
    C.FiniteRamsey := by
  intro Color _ _ colour
  obtain ⟨U, color, hU⟩ :=
    hScalarMilliken Color (fun X => colour (T.decodeFinite X))
  refine ⟨T.decodeInfinite U, color, ?_⟩
  intro S
  calc
    colour (C.refine (T.decodeInfinite U) S) =
        colour (T.decodeFinite
          (T.scalarRefine U (T.glueFinite S))) := by
            rw [T.refinement U S]
    _ = color := hU (T.glueFinite S)

/-- The full auxiliary-type-respecting Ramsey conclusion now follows
by the single scalar Milliken application and the two verified
coding-factorisation identities. No abstract unproved Ramsey
conclusion is inserted as an axiom. -/
theorem atrRamsey_of_rootGluedScalarMilliken
    (T : RootGluedMillikenTransfer C ScalarFin ScalarInf)
    (hScalarMilliken : T.ScalarFiniteRamsey)
    (Color : Type) [Fintype Color] [Nonempty Color]
    (χ : SmallEmb → Color) :
    ∃ f : LargeEmb, ∃ color : Color,
      ∀ e : SmallEmb, χ (C.act f e) = color :=
  C.auxRamsey_of_finiteRamsey
    (T.vectorFiniteRamsey_of_scalarMilliken hScalarMilliken)
    Color χ

end RootGluedMillikenTransfer
end ThreeUniformDiaries
