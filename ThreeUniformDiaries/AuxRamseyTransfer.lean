import Mathlib

/-!
# Transfer from canonical finite codes to the aux-type Ramsey theorem

The manuscript's finite-code identity is *not* that every embedding `e`
equals the image of a finite strong subtree: the intermediate embedding
`g_G ∘ e` lands in the universal branch hypergraph `K_I`.

We retain that extra branch layer in the interface. In manuscript notation:

* `branch e = g_G ∘ e`;
* `finiteBranch S = F_I^S ∘ g_A`;
* `outer B = φ ∘ B`;
* `lift U B = F_I^U ∘ B`;
* `decode U = φ ∘ F_I^U ∘ g_G`.

The three compatibility fields are exactly the finite extraction lemma,
canonical composition, and the construction of the infinite self-embedding.
The final Ramsey argument then follows solely from these identities and
the fixed-height finite-colour consequence of Milliken.
-/

namespace ThreeUniformDiaries

universe u₁ u₂ u₃ u₄ u₅

/-- The precise factorisation interfaces for the repaired aux-type Ramsey
proof, keeping the universal-branch hypergraph separate from the ambient
generic hypergraph. -/
structure AuxRamseyCoding
    (SmallEmb : Type u₁) (LargeEmb : Type u₂)
    (BranchEmb : Type u₃) (FinCode : Type u₄)
    (InfCode : Type u₅) where
  /-- Postcomposition by an aux-type-respecting ambient self-embedding. -/
  act : LargeEmb → SmallEmb → SmallEmb
  /-- `g_G ∘ e`, before applying the fixed outer embedding. -/
  branch : SmallEmb → BranchEmb
  /-- `F_I^S ∘ g_A`, before applying the fixed outer embedding. -/
  finiteBranch : FinCode → BranchEmb
  /-- The fixed outer embedding `φ : K_I → G`. -/
  outer : BranchEmb → SmallEmb
  /-- The canonical action of an infinite strong subtree on branch codes. -/
  lift : InfCode → BranchEmb → BranchEmb
  /-- The ambient self-embedding constructed from an infinite subtree. -/
  decode : InfCode → LargeEmb
  /-- Extract a finite strong subtree coding `g_G ∘ e`. -/
  encode : SmallEmb → FinCode
  /-- Strong completion inside the homogeneous infinite subtree. -/
  refine : InfCode → FinCode → FinCode
  /-- The finite encoding identity, corresponding to `lem:Aemb`. -/
  encode_spec : ∀ e, finiteBranch (encode e) = branch e
  /-- Canonical composition, corresponding to `lem:canonicalcomposition`. -/
  refine_spec :
    ∀ U S, finiteBranch (refine U S) = lift U (finiteBranch S)
  /-- Construction of the infinite embedding in the target, including `φ`. -/
  decode_spec :
    ∀ U e, act (decode U) e = outer (lift U (branch e))

namespace AuxRamseyCoding

variable {SmallEmb : Type u₁} {LargeEmb : Type u₂}
variable {BranchEmb : Type u₃} {FinCode : Type u₄}
variable {InfCode : Type u₅}

/-- The fixed-height vector-Milliken conclusion needed in the manuscript. -/
def FiniteRamsey
    (C : AuxRamseyCoding SmallEmb LargeEmb BranchEmb FinCode InfCode) : Prop :=
  ∀ (Color : Type) [Fintype Color] [Nonempty Color]
      (c : FinCode → Color),
    ∃ U : InfCode, ∃ color : Color,
      ∀ S : FinCode, c (C.refine U S) = color

/-- The manuscript's final Ramsey deduction, with no artificial
surjectivity assumption on the finite encoding. -/
theorem auxRamsey_of_finiteRamsey
    (C : AuxRamseyCoding SmallEmb LargeEmb BranchEmb FinCode InfCode)
    (hRamsey : C.FiniteRamsey)
    (Color : Type) [Fintype Color] [Nonempty Color]
    (χ : SmallEmb → Color) :
    ∃ f : LargeEmb, ∃ color : Color,
      ∀ e : SmallEmb, χ (C.act f e) = color := by
  let c : FinCode → Color := fun S => χ (C.outer (C.finiteBranch S))
  rcases hRamsey Color c with ⟨U, color, hU⟩
  refine ⟨C.decode U, color, ?_⟩
  intro e
  have h := hU (C.encode e)
  change χ (C.outer (C.finiteBranch (C.refine U (C.encode e)))) =
    color at h
  rw [C.refine_spec U (C.encode e), C.encode_spec e] at h
  rw [C.decode_spec U e]
  exact h

/-- Pairwise monochromaticity, matching the arrow-form conclusion. -/
theorem auxRamsey_pairwise
    (C : AuxRamseyCoding SmallEmb LargeEmb BranchEmb FinCode InfCode)
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
