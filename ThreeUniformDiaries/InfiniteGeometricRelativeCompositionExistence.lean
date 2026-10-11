import ThreeUniformDiaries.InfiniteGeometricRelativeBranchComposition
import ThreeUniformDiaries.InfiniteVectorGeometricComposition

/-!
# Existential geometric composition on the genuine relative K_I carrier

The full infinite geometric theorem constructs synchronized strong
pictures V2,V1,V0 and proves their entire E2/E1/E0 canonical maps
equal the pointwise composites. The checked relative-branch bridge
then transfers the E0 equation to EVERY vertex of K_I, provided both
constituent selected level maps fix the same finite initial cut.

This is the genuine existence-and-action form of the infinite-height
part of the manuscript's canonical composition lemma, without an
additional compositional field or a hypothesized candidate witness.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem exists_infiniteVector_geometric_relative_composition
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
    (hsigma : StrictMono sigma) (hf : StrictMono f)
    {n : Nat} (I : EnumNode n)
    (hfixS : ∀ i < n, sigma i = i)
    (hfixU : ∀ i < n, f i = i) :
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
        ∃ (hfixV : ∀ i < n, f (sigma i) = i),
        ∀ B : RelativeBranchNode I,
          (infiniteStrongPictureCanonicalMap hV₀ hV₁ hV₂
              (hf.comp hsigma)).relativeMapBranch_of_fixed_levels
              I hfixV B =
          (infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf)
            .relativeMapBranch_of_fixed_levels I hfixU
              ((infiniteStrongPictureCanonicalMap hS₀ hS₁ hS₂ hsigma)
                .relativeMapBranch_of_fixed_levels I hfixS B) := by
  obtain ⟨V₂, V₁, V₀, hV₂, hV₁, hV₀, _hAux, _hOne, hEnum⟩ :=
    exists_infiniteVector_geometric_composition
      hS₀ hS₁ hS₂ hU₀ hU₁ hU₂ hsigma hf
  have hfixV : ∀ i < n, f (sigma i) = i := by
    intro i hi
    rw [hfixS i hi, hfixU i hi]
  refine ⟨V₂, V₁, V₀, hV₂, hV₁, hV₀, hfixV, ?_⟩
  intro B
  exact infiniteVectorGeometric_relativeMapBranch_comp
    hS₀ hS₁ hS₂ hU₀ hU₁ hU₂ hV₀ hV₁ hV₂
    hsigma hf hEnum I hfixS hfixU hfixV B

end CoordNode
end ThreeUniformDiaries
