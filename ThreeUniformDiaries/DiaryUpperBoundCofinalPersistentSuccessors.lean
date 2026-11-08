import ThreeUniformDiaries.DiaryPersistentSuccessorBoundEquivalence
import ThreeUniformDiaries.DiaryUpperBoundUnlabelledCofinalHorizonBounds

/-!
# Track A: sharpen the cofinal upper interface to persistent successors

The exact pointwise equivalence persistentSuccessor_iff_cofinalBoundedNextLeafImages
is already kernel-verified on main (Track C integration #1231).
We lift it across the critical universal w0 / existential i / universal m,f
quantifiers in the verified sharp cofinal-horizon diary upper theorems.

This is an exact equivalence of TWO SUFFICIENT HYPOTHESES. No proof
that either condition holds in arbitrary prescribed generic leaf
ranges is claimed, and no assertion about unconditional countable
diary unavoidability or the full diary Ramsey theorem is made.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Every ordinary induced universal selfcopy w₀ admits a further
unordered selfcopy i such that EVERY finitely persistent genuine leaf
stage in the selected range has a compatible persistent successor.
All the old support values are fixed literally. The refinement i
is chosen BEFORE the source stage m,f, not separately for each stage. -/
def HasCofinalPersistentSuccessorRefinement
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H) (F : UnorderedEmbedding U H) : Prop :=
  ∀ w₀ : UnorderedEmbedding U U,
    ∃ i : UnorderedEmbedding U U,
      ∀ m : Nat, IsLeaf H m →
        ∀ f : Nat → Nat,
          PersistentReservedDiaryStage H H
            (fun t => F (w₀ (i t))) m f →
          ∃ g : Nat → Nat,
            PersistentReservedDiaryStage H H
              (fun t => F (w₀ (i t))) (m + 1) g ∧
            CofinalDiaryStageCompatible H m f g

/-- Exactly the cofinal bounded-image condition already used by the
sharp labelled and unlabelled Track A upper theorems.
No compactness or new geometric existence premise is introduced. -/
theorem cofinalPersistentSuccessorRefinement_iff_cofinalHorizonBounds
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H) (F : UnorderedEmbedding U H) :
    HasCofinalPersistentSuccessorRefinement D F ↔
      HasCofinalHorizonBoundedNextLeafImages D F := by
  constructor
  · intro hExtend w₀
    obtain ⟨i, hi⟩ := hExtend w₀
    refine ⟨i, ?_⟩
    intro m hm f hf
    exact (persistentSuccessor_iff_cofinalBoundedNextLeafImages hm).mp
      (hi m hm f hf)
  · intro hBounds w₀
    obtain ⟨i, hi⟩ := hBounds w₀
    refine ⟨i, ?_⟩
    intro m hm f hf
    exact (persistentSuccessor_iff_cofinalBoundedNextLeafImages hm).mpr
      (hi m hm f hf)

/-- Conditional sharp LABELLED diary upper with exactly one
automorphism-group factor. The cofinal successor hypothesis remains
an independently unproved geometric premise. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_cofinalPersistentSuccessors
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsDiaryLeafLabelledCopy A H v} → κ)
    (hExtend : HasCofinalPersistentSuccessorRefinement D F) :
    ∃ (h : Ordered3Graph.Embedding H H)
      (palette : List κ),
        palette.length =
          (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        h.TypeRespecting ∧
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        ∀ v : Fin a → Nat,
          IsDiaryLeafLabelledCopy A H v →
          ∃ hOutput :
              IsDiaryLeafLabelledCopy A H (fun j => h (v j)),
            χ ⟨(fun j => h (v j)), hOutput⟩ ∈ palette := by
  exact actualFiniteAuxRamsey_allDiaryLeaf_upper_of_cofinalHorizonBounds
    U H D F hLeaf hUniversal A χ
    ((cofinalPersistentSuccessorRefinement_iff_cofinalHorizonBounds D F).mp
      hExtend)

/-- Separate conditional sharp UNLABELLED upper on total finite-set
colourings, with NO automorphism-group factor. This is not inferred
by dividing the labelled degree. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_unlabelled_upper_of_cofinalPersistentSuccessors
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Finset Nat → κ)
    (hExtend : HasCofinalPersistentSuccessorRefinement D F) :
    ∃ (h : Ordered3Graph.Embedding H H)
      (palette : List κ),
        palette.length =
          (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) ∧
        h.TypeRespecting ∧
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        ∀ v : Fin a → Nat,
          IsDiaryLeafLabelledCopy A H v →
          ∃ hOutput :
              IsDiaryLeafLabelledCopy A H (fun j => h (v j)),
            χ ((Finset.univ : Finset (Fin a)).image
              (fun j => h (v j))) ∈ palette := by
  exact actualFiniteAuxRamsey_allDiaryLeaf_unlabelled_upper_of_cofinalHorizonBounds
    U H D F hLeaf hUniversal A χ
    ((cofinalPersistentSuccessorRefinement_iff_cofinalHorizonBounds D F).mp
      hExtend)

end ATRFiniteDecoder
end ThreeUniformDiaries
