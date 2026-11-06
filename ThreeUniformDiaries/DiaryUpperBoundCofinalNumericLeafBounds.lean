import ThreeUniformDiaries.DiaryUpperBoundCofinalPersistentFiniteCovers
import ThreeUniformDiaries.DiaryFiniteNextLeafCoverBounds

/-!
# Track A: a purely NUMERICAL cofinal next-leaf bound criterion

The finite-cover interface for the stronger sharp diary upper theorem
can be stated without Finset-valued witnesses: a finite cover at
all finite horizons is equivalent to ONE uniformly bounded new
target leaf image. We prove exact equivalence of these two COFINAL
conditions, then offer a useful sufficient criterion where the
PREIMAGE INDEX in the prescribed outer leaf-range F∘w₀∘i
is bounded instead. The outer leaf embedding F may be unordered.

The sharp diary upper result still requires that for every
candidate upper selfcopy w₀ some further i has these uniform
finite-horizon bounds at every finitely persistent stage. This is
an independently OPEN Track D target, not an assertion that
every finite-stage tree has an infinite branch. No countable
diary Ramsey theorem is assumed.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- Uniform NUMERICAL target-image bounds, after SOME further
induced subcopy of every ordinary upper selfcopy. These must
hold for every finitely persistent source leaf stage, and are
not implied by bounded old-new MEET levels alone. -/
def HasCofinalUniformNextImageBounds
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H) : Prop :=
  ∀ w₀ : UnorderedEmbedding U U,
    ∃ i : UnorderedEmbedding U U,
      ∀ m : Nat, IsLeaf H m →
        ∀ f : Nat → Nat,
          PersistentReservedDiaryStage H H
            (fun t => F (w₀ (i t))) m f →
          ∃ B : Nat, ∀ n : Nat, ∃ g : Nat → Nat,
            ReservedDiaryStage H H
              (fun t => F (w₀ (i t))) (m + 1 + n) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m ≤ B

/-- The abstract finite-cover condition and the concrete UNIFORM
NUMERICAL next-leaf-image boundedness are exactly equivalent,
with the quantifiers preserving the same cofinal refinement i. -/
theorem cofinalFiniteCover_iff_uniformNextImageBound
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H) :
    HasCofinalPersistentFiniteNextLeafCovers D F ↔
      HasCofinalUniformNextImageBounds D F := by
  constructor
  · intro hCover w₀
    obtain ⟨i, hi⟩ := hCover w₀
    refine ⟨i, ?_⟩
    intro m hm f hf
    exact (finiteHorizonNextLeafCover_iff_uniform_image_bound
      H H (fun t => F (w₀ (i t))) m f).mp (hi m hm f hf)
  · intro hBound w₀
    obtain ⟨i, hi⟩ := hBound w₀
    refine ⟨i, ?_⟩
    intro m hm f hf
    exact (finiteHorizonNextLeafCover_iff_uniform_image_bound
      H H (fun t => F (w₀ (i t))) m f).mpr (hi m hm f hf)

/-- A particularly concrete sufficient condition: after further
refinement, every persistent stage has a fixed FINITE bound B on
the index t of a possible new leaf image in the prescribed range
F[w₀(i[U])], uniformly over all later finite horizons.

The next target vertex need NOT be numerically monotone in t:
finiteness of the source-index interval is enough. -/
def HasCofinalBoundedNextLeafRangeIndices
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H) : Prop :=
  ∀ w₀ : UnorderedEmbedding U U,
    ∃ i : UnorderedEmbedding U U,
      ∀ m : Nat, IsLeaf H m →
        ∀ f : Nat → Nat,
          PersistentReservedDiaryStage H H
            (fun t => F (w₀ (i t))) m f →
          ∃ B : Nat, ∀ n : Nat, ∃ g : Nat → Nat,
            ReservedDiaryStage H H
              (fun t => F (w₀ (i t))) (m + 1 + n) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            ∃ t : Nat, t < B ∧ g m = F (w₀ (i t))

/-- Uniform bounds on the NEXT LEAF'S PREIMAGE INDEX
supply the finite-set covers used by the checked conditional
countable diary fusion: W can be the image of range B. -/
theorem hasCofinalFiniteCovers_of_bounded_next_leaf_indices
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hIndex : HasCofinalBoundedNextLeafRangeIndices D F) :
    HasCofinalPersistentFiniteNextLeafCovers D F := by
  intro w₀
  obtain ⟨i, hi⟩ := hIndex w₀
  refine ⟨i, ?_⟩
  intro m hm f hf
  exact finiteHorizonNextLeafCover_of_bounded_preimage_index
    H H (fun t => F (w₀ (i t))) m f (hi m hm f hf)

/-- FULL sharp labelled diary upper bound, with all genuine
leaf A-copies stabilized by one marker-fixed, TypeRespecting
diary selfembedding, under the concrete cofinal bound on
next-leaf preimage indices in the prescribed range.

No supplied generic G, no order/surjectivity assumption on F,
and no hypothetical countable diary unavoidability are used.
The preimage-index boundedness hypothesis remains OPEN. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_cofinal_bounded_indices
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsDiaryLeafLabelledCopy A H v} → κ)
    (hIndex : HasCofinalBoundedNextLeafRangeIndices D F) :
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
  exact actualFiniteAuxRamsey_allDiaryLeaf_upper_of_cofinal_finite_covers
    U H D F hLeaf hUniversal A χ
    (hasCofinalFiniteCovers_of_bounded_next_leaf_indices
      D F hIndex)

end ATRFiniteDecoder
end ThreeUniformDiaries
