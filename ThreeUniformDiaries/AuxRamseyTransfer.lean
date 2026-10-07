import Mathlib

/-!
# The canonical-code transfer step in the aux-type Ramsey proof

The repaired manuscript proof has four genuinely separate ingredients:

* every finite aux-type-respecting embedding has a finite strong-tree code;
* every infinite code gives an aux-type-respecting self-embedding;
* finite canonical codes compose with an infinite code;
* Milliken makes all finite codes below one infinite code monochromatic.

This file formalizes the final implication from precisely those interfaces.
No combinatorial theorem is postulated as an axiom: the Milliken conclusion
is an explicit hypothesis, to be discharged by the concrete tree
formalization.
-/

namespace ThreeUniformDiaries

universe u₁ u₂ u₃ u₄

/-- Abstract interface of the canonical maps occurring in the repaired proof.

`SmallEmb` represents embeddings of the fixed finite hypergraph,
`LargeEmb` self-embeddings of the generic hypergraph,
`FinCode` finite strong-vector-subtree codes, and `InfCode` infinite ones.
-/
structure AuxRamseyCoding
    (SmallEmb : Type u₁) (LargeEmb : Type u₂)
    (FinCode : Type u₃) (InfCode : Type u₄) where
  act : LargeEmb → SmallEmb → SmallEmb
  realize : FinCode → SmallEmb
  encode : SmallEmb → FinCode
  decode : InfCode → LargeEmb
  refine : InfCode → FinCode → FinCode
  encode_spec : ∀ e, realize (encode e) = e
  composition :
    ∀ U S, realize (refine U S) = act (decode U) (realize S)

namespace AuxRamseyCoding

variable {SmallEmb : Type u₁} {LargeEmb : Type u₂}
variable {FinCode : Type u₃} {InfCode : Type u₄}

/-- The exact finite-colour conclusion needed from vector Milliken. -/
def FiniteRamsey
    (C : AuxRamseyCoding SmallEmb LargeEmb FinCode InfCode) : Prop :=
  ∀ (Color : Type) [Fintype Color] [Nonempty Color]
      (c : FinCode → Color),
    ∃ U : InfCode, ∃ color : Color,
      ∀ S : FinCode, c (C.refine U S) = color

/-- Canonical coding plus the finite-colour Milliken conclusion imply the
aux-type Ramsey theorem.

This is the formal version of the last paragraph of the repaired proof:
encode an arbitrary finite embedding, compose its code with the homogeneous
infinite code, and use the canonical-composition identity. -/
theorem auxRamsey_of_finiteRamsey
    (C : AuxRamseyCoding SmallEmb LargeEmb FinCode InfCode)
    (hRamsey : C.FiniteRamsey)
    (Color : Type) [Fintype Color] [Nonempty Color]
    (χ : SmallEmb → Color) :
    ∃ f : LargeEmb, ∃ color : Color,
      ∀ e : SmallEmb, χ (C.act f e) = color := by
  let c : FinCode → Color := fun S => χ (C.realize S)
  rcases hRamsey Color c with ⟨U, color, hU⟩
  refine ⟨C.decode U, color, ?_⟩
  intro e
  have h := hU (C.encode e)
  rw [C.composition U (C.encode e), C.encode_spec e] at h
  exact h

/-- Pairwise-constant formulation matching the usual arrow notation. -/
theorem auxRamsey_pairwise
    (C : AuxRamseyCoding SmallEmb LargeEmb FinCode InfCode)
    (hRamsey : C.FiniteRamsey)
    (Color : Type) [Fintype Color] [Nonempty Color]
    (χ : SmallEmb → Color) :
    ∃ f : LargeEmb,
      ∀ e₀ e₁ : SmallEmb,
        χ (C.act f e₀) = χ (C.act f e₁) := by
  rcases C.auxRamsey_of_finiteRamsey hRamsey Color χ with
    ⟨f, color, hf⟩
  refine ⟨f, ?_⟩
  intro e₀ e₁
  exact (hf e₀).trans (hf e₁).symm

end AuxRamseyCoding
end ThreeUniformDiaries
