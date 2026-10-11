import ThreeUniformDiaries.InfiniteOneGeometricComposition
import ThreeUniformDiaries.InfiniteEnumCompositeSuccessor
import ThreeUniformDiaries.InfiniteEnumCanonicalUniqueness

/-!
# FULL infinite geometric composition in all three type-tree coordinates

Two synchronized triples of genuine infinite strong type-tree
pictures with selected levels sigma and f have a synchronized
composite strong triple V2,V1,V0 at selected levels f ∘ sigma.

Every V-coordinate is constructed literally by protected completion
of the inner geometric image INSIDE the corresponding outer U-coordinate.
The genuine recursively defined canonical maps agree at EVERY source
node with the pointwise composites. E2 was proved first, E1 second
using E2 as its complete successor parameter, and E0 last using
the already identified complete E1 parameter.

This does not invoke an abstract CanonicalMap compatibility axiom;
the concrete composite successor cones and the canonical uniqueness
theorems supply exactly the missing geometric identity.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem exists_infiniteVector_geometric_composition
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
        V₂ ⊆ U₂ ∧ V₁ ⊆ U₁ ∧ V₀ ⊆ U₀ ∧
        (∀ n (c : AuxNode n),
          (infiniteAuxCanonicalMap hV₂ n c).val =
            (infiniteAuxCanonicalMap hU₂ (sigma n)
              (infiniteAuxCanonicalMap hS₂ n c).val).val) ∧
        (∀ n (b : OneNode n),
          (infiniteOneCanonicalMap hV₁ hV₂ n b).val =
            (infiniteOneCanonicalMap hU₁ hU₂ (sigma n)
              (infiniteOneCanonicalMap hS₁ hS₂ n b).val).val) ∧
        (∀ n (a : EnumNode n),
          (infiniteEnumCanonicalMap hV₀ hV₁ hV₂ n a).val =
            (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma n)
              (infiniteEnumCanonicalMap hS₀ hS₁ hS₂ n a).val).val) := by
  obtain ⟨V₂, V₁, hV₂, hV₁, hVU₂, hVU₁, hAux, hOne⟩ :=
    exists_infiniteOne_geometric_composition
      hS₁ hS₂ hU₁ hU₂ hsigma hf
  obtain ⟨V₀, hV₀, hVU₀, hEV⟩ :=
    exists_infiniteEnum_image_completion
      hS₀ hS₁ hS₂ hU₀ hU₁ hU₂ hsigma hf
  let G₁ : (n : Nat) → OneNode n → OneNode (f (sigma n)) :=
    fun n b =>
      (infiniteOneCanonicalMap hU₁ hU₂ (sigma n)
        (infiniteOneCanonicalMap hS₁ hS₂ n b).val).val
  let G₀ : (n : Nat) → EnumNode n → EnumNode (f (sigma n)) :=
    fun n a =>
      (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma n)
        (infiniteEnumCanonicalMap hS₀ hS₁ hS₂ n a).val).val
  have hG₁ : ∀ n (b : OneNode n),
      G₁ n b = (infiniteOneCanonicalMap hV₁ hV₂ n b).val := by
    intro n b
    exact (hOne n b).symm
  have hmem : ∀ n (a : EnumNode n),
      CoordNode.enum (f (sigma n)) (G₀ n a) ∈ V₀ := by
    intro n a
    apply hEV
    exact ⟨sigma n, (infiniteEnumCanonicalMap hS₀ hS₁ hS₂ n a).val,
      (infiniteEnumCanonicalMap hS₀ hS₁ hS₂ n a).property, rfl⟩
  have hroot : ∀ a : EnumNode 0,
      G₀ 0 a =
        (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma 0) rS₀).val := by
    intro a
    change (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma 0)
      (infiniteEnumCanonicalMap hS₀ hS₁ hS₂ 0 a).val).val =
      (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma 0) rS₀).val
    rw [infiniteEnumCanonicalMap_root hS₀ hS₁ hS₂ a]
  have hsucc : ∀ n (a : EnumNode n) (b : OneNode n),
      CoordNode.enum (f (sigma n) + 1)
        ((G₀ n a).succ (G₁ n b)) ≤
      CoordNode.enum (f (sigma (n + 1)))
        (G₀ (n + 1) (a.succ b)) := by
    intro n a b
    exact infiniteEnumCanonicalMap_composite_succ
      hS₀ hS₁ hS₂ hU₀ hU₁ hU₂ hsigma hf n a b
  have heq := infiniteEnumCanonicalMap_unique_of_cones
    hV₀ hV₁ hV₂ G₁ G₀ hG₁ hmem hroot hsucc
  refine ⟨V₂, V₁, V₀, hV₂, hV₁, hV₀, hVU₂, hVU₁, hVU₀, hAux, hOne, ?_⟩
  intro n a
  exact (heq n a).symm

end CoordNode
end ThreeUniformDiaries
