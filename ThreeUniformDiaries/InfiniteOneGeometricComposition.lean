import ThreeUniformDiaries.InfiniteCanonicalImageCompletions
import ThreeUniformDiaries.InfiniteAuxGeometricComposition
import ThreeUniformDiaries.InfiniteOneCanonicalUniqueness
import ThreeUniformDiaries.InfiniteOneCompositeSuccessor

/-!
# Genuine geometric composition in BOTH E2 and E1 coordinates

First choose an actual E2 strong picture V2 with the pointwise
composite auxiliary map, using the checked E2 geometric composition.
Then complete the E1 image inside U1, with precisely the same
composed selected levels. The composite E1 map lands in this
strong picture, fixes the composed root and enters precisely the
cone prescribed by the ALREADY IDENTIFIED E2 parameter map.
Triangular uniqueness identifies its genuine recursive E1 map.

No abstract CanonicalMap compatibility field is postulated.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem exists_infiniteOne_geometric_composition
    {S₁ S₂ U₁ U₂ : Set CoordNode} {sigma f : Nat → Nat}
    {rS₁ : OneNode (sigma 0)} {rS₂ : AuxNode (sigma 0)}
    {rU₁ : OneNode (f 0)} {rU₂ : AuxNode (f 0)}
    (hS₁ : InfiniteStrongPicture S₁ sigma (.one (sigma 0) rS₁))
    (hS₂ : InfiniteStrongPicture S₂ sigma (.aux (sigma 0) rS₂))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f) :
    ∃ (V₂ V₁ : Set CoordNode),
      ∃ (hV₂ : InfiniteStrongPicture V₂ (fun i => f (sigma i))
        (.aux (f (sigma 0))
          (infiniteAuxCanonicalMap hU₂ (sigma 0) rS₂).val))
        (hV₁ : InfiniteStrongPicture V₁ (fun i => f (sigma i))
        (.one (f (sigma 0))
          (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0) rS₁).val)),
        (∀ n (c : AuxNode n),
          (infiniteAuxCanonicalMap hV₂ n c).val =
            (infiniteAuxCanonicalMap hU₂ (sigma n)
              (infiniteAuxCanonicalMap hS₂ n c).val).val) ∧
        (∀ n (a : OneNode n),
          (infiniteOneCanonicalMap hV₁ hV₂ n a).val =
            (infiniteOneCanonicalMap hU₁ hU₂ (sigma n)
              (infiniteOneCanonicalMap hS₁ hS₂ n a).val).val) := by
  obtain ⟨V₂, hV₂, hAux⟩ :=
    exists_infiniteAux_geometric_composition
      hS₂ hU₂ hsigma hf
  obtain ⟨V₁, hV₁, hEV⟩ :=
    exists_infiniteOne_image_completion
      hS₁ hS₂ hU₁ hU₂ hsigma hf
  let G₂ : (n : Nat) → AuxNode n → AuxNode (f (sigma n)) :=
    fun n c =>
      (infiniteAuxCanonicalMap hU₂ (sigma n)
        (infiniteAuxCanonicalMap hS₂ n c).val).val
  let G₁ : (n : Nat) → OneNode n → OneNode (f (sigma n)) :=
    fun n a =>
      (infiniteOneCanonicalMap hU₁ hU₂ (sigma n)
        (infiniteOneCanonicalMap hS₁ hS₂ n a).val).val
  have hG₂ : ∀ n (c : AuxNode n),
      G₂ n c = (infiniteAuxCanonicalMap hV₂ n c).val := by
    intro n c
    exact (hAux n c).symm
  have hmem : ∀ n (a : OneNode n),
      CoordNode.one (f (sigma n)) (G₁ n a) ∈ V₁ := by
    intro n a
    apply hEV
    exact ⟨sigma n, (infiniteOneCanonicalMap hS₁ hS₂ n a).val,
      (infiniteOneCanonicalMap hS₁ hS₂ n a).property, rfl⟩
  have hroot : ∀ a : OneNode 0,
      G₁ 0 a = (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0) rS₁).val := by
    intro a
    change (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0)
      (infiniteOneCanonicalMap hS₁ hS₂ 0 a).val).val =
      (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0) rS₁).val
    rw [infiniteOneCanonicalMap_root hS₁ hS₂ a]
  have hsucc : ∀ n (a : OneNode n) (c : AuxNode n),
      CoordNode.one (f (sigma n) + 1) ((G₁ n a).succ (G₂ n c)) ≤
        CoordNode.one (f (sigma (n + 1)))
          (G₁ (n + 1) (a.succ c)) := by
    intro n a c
    exact infiniteOneCanonicalMap_composite_succ
      hS₁ hS₂ hU₁ hU₂ hsigma hf n a c
  have heq := infiniteOneCanonicalMap_unique_of_cones
    hV₁ hV₂ G₂ G₁ hG₂ hmem hroot hsucc
  refine ⟨V₂, V₁, hV₂, hV₁, hAux, ?_⟩
  intro n a
  exact (heq n a).symm

end CoordNode
end ThreeUniformDiaries
