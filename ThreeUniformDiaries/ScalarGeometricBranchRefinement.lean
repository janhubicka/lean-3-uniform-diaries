import ThreeUniformDiaries.RootGluedVectorRefinement
import ThreeUniformDiaries.InfiniteGeometricRelativeBranchComposition

/-!
# Genuine scalar refinement realizing composition of F_I canonical maps

The abstract AuxRamseyCoding interface requires a real refinement:
if a finite or infinite strong picture S is encoded inside a
Milliken-selected picture U, the composed picture V must satisfy
V ≤ U in the ACTUAL scalar rooted tree, while its canonical branch
map equals F_U ∘ F_S.

Previously, these facts were scattered between root-glued
refinement geometry and canonical-map composition, and the
coordinatewise containment V_i ⊆ U_i was not exported by the old
composition API.

The newly checked stronger geometric composition lemma now gives
both properties at once. This theorem joins them without a
hypothetical scalar/vector equivalence or a separate containment
axiom. It is the infinite part of the concrete ATR realization law.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Geometrically compose two actual strong E0/E1/E2 vectors;
their genuine root-glued scalar strong subtree REFines the outer
one, and the canonical branch action composes on every K-empty
vertex exactly. -/
theorem exists_scalar_geometric_refinement_with_branch_composition
    {S₀ S₁ S₂ U₀ U₁ U₂ : Set CoordNode} {sigma f : Nat → Nat}
    {rS₀ : EnumNode (sigma 0)} {rS₁ : OneNode (sigma 0)}
    {rS₂ : AuxNode (sigma 0)}
    {rU₀ : EnumNode (f 0)} {rU₁ : OneNode (f 0)}
    {rU₂ : AuxNode (f 0)}
    (hS₀ : InfiniteStrongPicture S₀ sigma (.enum (sigma 0) rS₀))
    (hS₁ : InfiniteStrongPicture S₁ sigma (.one (sigma 0) rS₁))
    (hS₂ : InfiniteStrongPicture S₂ sigma (.aux (sigma 0) rS₂))
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) rU₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f) :
    ∃ (V₂ V₁ V₀ : Set CoordNode),
      ∃ (hV₂ : InfiniteStrongPicture V₂ (fun i => f (sigma i))
        (.aux (f (sigma 0))
          (infiniteAuxCanonicalMap hU₂ (sigma 0) rS₂).val))
        (hV₁ : InfiniteStrongPicture V₁ (fun i => f (sigma i))
        (.one (f (sigma 0))
          (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0) rS₁).val))
        (hV₀ : InfiniteStrongPicture V₀ (fun i => f (sigma i))
        (.enum (f (sigma 0))
          (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma 0) rS₀).val)),
        (gluedVectorStrong_to_milliken hV₀ hV₁ hV₂
            (hf.comp hsigma)).Refines
          (gluedVectorStrong_to_milliken hU₀ hU₁ hU₂ hf) ∧
        ∀ B : EnumerationBranchNode,
          (infiniteStrongPictureCanonicalMap
            hV₀ hV₁ hV₂ (hf.comp hsigma)).mapBranch B =
          (infiniteStrongPictureCanonicalMap
            hU₀ hU₁ hU₂ hf).mapBranch
            ((infiniteStrongPictureCanonicalMap
              hS₀ hS₁ hS₂ hsigma).mapBranch B) := by
  obtain ⟨V₂, V₁, V₀, hV₂, hV₁, hV₀,
      hVU₂, hVU₁, hVU₀, hAux, hOne, hEnum⟩ :=
    exists_infiniteVector_geometric_composition_with_subset
      hS₀ hS₁ hS₂ hU₀ hU₁ hU₂ hsigma hf
  refine ⟨V₂, V₁, V₀, hV₂, hV₁, hV₀, ?_, ?_⟩
  · exact (gluedVectorStrong_refines_iff
      hV₀ hV₁ hV₂ (hf.comp hsigma)
      hU₀ hU₁ hU₂ hf).mpr
      ⟨hVU₀, hVU₁, hVU₂⟩
  · intro B
    exact infiniteVectorGeometric_mapBranch_comp
      hS₀ hS₁ hS₂ hU₀ hU₁ hU₂ hV₀ hV₁ hV₂
      hsigma hf hEnum B

end CoordNode
end ThreeUniformDiaries
