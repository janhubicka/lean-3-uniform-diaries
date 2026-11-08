import ThreeUniformDiaries.DiaryCofinalBoundedCountableFusion
import ThreeUniformDiaries.DiaryUpperBoundCofinalNumericLeafBounds

/-!
# Track A: sharp diary upper from bounded next leaf images at COFINAL horizons

The checked Track A upper theorem requires an explicitly supplied
cofinal finite-cover certificate, equivalently a uniform numerical
next-leaf bound at every finite horizon. The Track D reduction
HasCofinalBoundedNextLeafImages needs the SAME bound only along
ARBITRARILY LARGE finite horizons. Genuine reserved-stage restriction
provides all intermediate horizons without changing the actual
images or old-support agreement.

Here we package the exact equivalence after the extra unordered
selfcopy refinement i permitted by the verified sharp cofinal
upper theorem. This gives the SHARP labelled diary-upper palette
under a concrete cofinal-horizon boundedness hypothesis.

This is NOT an unconditional theorem: no bound is constructed
from genericity, finite absorption, tail cones, or infinite
compactness. The strengthened countable diary Ramsey and
countable unavoidability statements remain separate.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- At every ordinary universal selfcopy w₀ there is some further
unordered induced selfcopy i such that every finitely persistent
source leaf stage in F[w₀(i[U])] has ONE bounded next target image
along arbitrarily high finite horizons. There is no infinite
embedding in this definition. -/
def HasCofinalHorizonBoundedNextLeafImages
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H) (F : UnorderedEmbedding U H) : Prop :=
  ∀ w₀ : UnorderedEmbedding U U,
    ∃ i : UnorderedEmbedding U U,
      ∀ m : Nat, IsLeaf H m →
        ∀ f : Nat → Nat,
          PersistentReservedDiaryStage H H
            (fun t => F (w₀ (i t))) m f →
          HasCofinalBoundedNextLeafImages H H
            (fun t => F (w₀ (i t))) f m

/-- The weaker-looking cofinal-horizon condition is EXACTLY the
uniform-at-every-horizon image-bound condition. The same further
copy i and the same bound B work in both directions, because
the reserved horizon witnesses restrict without changing images. -/
theorem cofinalHorizonBounds_iff_uniformNextImageBounds
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H) (F : UnorderedEmbedding U H) :
    HasCofinalHorizonBoundedNextLeafImages D F ↔
      HasCofinalUniformNextImageBounds D F := by
  constructor
  · intro hCofinal w₀
    obtain ⟨i, hi⟩ := hCofinal w₀
    refine ⟨i, ?_⟩
    intro m hm f hf
    obtain ⟨B, hAll⟩ := hi m hm f hf
    refine ⟨B, ?_⟩
    intro N
    obtain ⟨n, hNn, g, Q, hCompat, hBound⟩ := hAll N
    exact ⟨g, Q.restrict (by omega), hCompat, hBound⟩
  · intro hUniform w₀
    obtain ⟨i, hi⟩ := hUniform w₀
    refine ⟨i, ?_⟩
    intro m hm f hf
    obtain ⟨B, hAll⟩ := hi m hm f hf
    refine ⟨B, ?_⟩
    intro N
    obtain ⟨g, Q, hCompat, hBound⟩ := hAll N
    exact ⟨N, le_rfl, g, Q, hCompat, hBound⟩

/-- Equivalently, the earlier finite-cover criterion for the
cofinal certified fusion sharp upper is satisfied precisely
when bounded candidate next target leaves occur at COFINALLY
LARGE finite horizons after a further universal subcopy. -/
theorem cofinalHorizonBounds_iff_finiteNextLeafCovers
    {U H : Ordered3Graph Nat}
    (D : RoleDiary H) (F : UnorderedEmbedding U H) :
    HasCofinalHorizonBoundedNextLeafImages D F ↔
      HasCofinalPersistentFiniteNextLeafCovers D F :=
  (cofinalHorizonBounds_iff_uniformNextImageBounds D F).trans
    (cofinalFiniteCover_iff_uniformNextImageBound D F).symm

/-- A completely explicit conditional sharp diary upper theorem:
bounded compatible next-leaf images are required only along
cofinally many finite horizons, and only after a further
induced universal selfcopy selected for each ordinary w₀.

The conclusion is a marker-fixed, fully TypeRespecting induced
diary selfembedding with the exact all-ordered-presentations
labelled palette on EVERY genuine diary leaf A-copy.
No supplied generic G or monotonicity/surjectivity of F. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_cofinalHorizonBounds
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsDiaryLeafLabelledCopy A H v} → κ)
    (hBounds : HasCofinalHorizonBoundedNextLeafImages D F) :
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
    ((cofinalHorizonBounds_iff_finiteNextLeafCovers D F).mp hBounds)

end ATRFiniteDecoder
end ThreeUniformDiaries
