import ThreeUniformDiaries.InfiniteStrongCompleteFixedPrefix

/-!
# Full anchored prefix for a synchronized composite strong vector picture

The type-tree geometric composition theorem produces three strong
coordinate pictures at the SAME composed selected level map f∘sigma.
If both original maps fix each level <n, so does their composition.
The preceding exact coordinate lemmas therefore imply that every
ambient E2/E1/E0 type-tree node at each level <n is present in V.

This is the complete anchored Str_{n,omega} condition, not just
fixation of the first n enumeration vertices along one branch.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteVectorStrongPicture_completePrefix
    {V₀ V₁ V₂ : Set CoordNode} {sigma f : Nat → Nat}
    {rV₀ : EnumNode (f (sigma 0))}
    {rV₁ : OneNode (f (sigma 0))}
    {rV₂ : AuxNode (f (sigma 0))}
    (hV₀ : InfiniteStrongPicture V₀ (fun i => f (sigma i))
      (.enum (f (sigma 0)) rV₀))
    (hV₁ : InfiniteStrongPicture V₁ (fun i => f (sigma i))
      (.one (f (sigma 0)) rV₁))
    (hV₂ : InfiniteStrongPicture V₂ (fun i => f (sigma i))
      (.aux (f (sigma 0)) rV₂))
    (hf : StrictMono f) (hsigma : StrictMono sigma)
    {n : Nat}
    (hfixU : ∀ i < n, f i = i)
    (hfixS : ∀ i < n, sigma i = i) :
    (∀ i : Nat, i < n → ∀ c : AuxNode i,
      CoordNode.aux i c ∈ V₂) ∧
    (∀ i : Nat, i < n → ∀ b : OneNode i,
      CoordNode.one i b ∈ V₁) ∧
    (∀ i : Nat, i < n → ∀ a : EnumNode i,
      CoordNode.enum i a ∈ V₀) := by
  have hfix : ∀ i < n, f (sigma i) = i := by
    intro i hi
    rw [hfixS i hi, hfixU i hi]
  refine ⟨?_, ?_, ?_⟩
  · exact infiniteAuxStrongPicture_completePrefix
      hV₂ (hf.comp hsigma) hfix
  · exact infiniteOneStrongPicture_completePrefix
      hV₁ hV₂ (hf.comp hsigma) hfix
  · exact infiniteEnumStrongPicture_completePrefix
      hV₀ hV₁ hV₂ (hf.comp hsigma) hfix

end CoordNode
end ThreeUniformDiaries
