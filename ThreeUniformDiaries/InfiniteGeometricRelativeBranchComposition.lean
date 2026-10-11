import ThreeUniformDiaries.InfiniteVectorGeometricComposition
import ThreeUniformDiaries.InfiniteCanonicalRecord
import ThreeUniformDiaries.CanonicalRelativeFixedLevels
import ThreeUniformDiaries.CanonicalBranchComposition

/-!
# Actual geometric canonical composition on ALL relative K_I branches

The concrete three-coordinate strong-picture theorem already gives
exact equality of the enumeration canonical maps under composition.
The canonical branch action uses ONLY that enumeration map and the
selected level map. Therefore the actual geometric canonical branch
action agrees pointwise with the algebraic CanonicalMap composite.

When both input level maps fix an initial segment of size n, so does
their composite. The verified fixed-levels relative carrier theorem
makes each of the three actual branch actions an endomap of K_I,
and they compose literally on EVERY vertex of that carrier.

This is a geometric-to-algebraic interface; the existence of V is
supplied separately by exists_infiniteVector_geometric_composition.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteVectorGeometric_mapBranch_comp
    {S₀ S₁ S₂ U₀ U₁ U₂ V₀ V₁ V₂ : Set CoordNode}
    {sigma f : Nat → Nat}
    {rS₀ : EnumNode (sigma 0)} {rS₁ : OneNode (sigma 0)}
    {rS₂ : AuxNode (sigma 0)}
    {rU₀ : EnumNode (f 0)} {rU₁ : OneNode (f 0)}
    {rU₂ : AuxNode (f 0)}
    {rV₀ : EnumNode (f (sigma 0))}
    {rV₁ : OneNode (f (sigma 0))}
    {rV₂ : AuxNode (f (sigma 0))}
    (hS₀ : InfiniteStrongPicture S₀ sigma (.enum (sigma 0) rS₀))
    (hS₁ : InfiniteStrongPicture S₁ sigma (.one (sigma 0) rS₁))
    (hS₂ : InfiniteStrongPicture S₂ sigma (.aux (sigma 0) rS₂))
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) rU₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hV₀ : InfiniteStrongPicture V₀ (fun i => f (sigma i))
      (.enum (f (sigma 0)) rV₀))
    (hV₁ : InfiniteStrongPicture V₁ (fun i => f (sigma i))
      (.one (f (sigma 0)) rV₁))
    (hV₂ : InfiniteStrongPicture V₂ (fun i => f (sigma i))
      (.aux (f (sigma 0)) rV₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f)
    (hEnum : ∀ n (a : EnumNode n),
      (infiniteEnumCanonicalMap hV₀ hV₁ hV₂ n a).val =
        (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma n)
          (infiniteEnumCanonicalMap hS₀ hS₁ hS₂ n a).val).val)
    (B : EnumerationBranchNode) :
    (infiniteStrongPictureCanonicalMap hV₀ hV₁ hV₂
      (hf.comp hsigma)).mapBranch B =
      (infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch
        ((infiniteStrongPictureCanonicalMap hS₀ hS₁ hS₂ hsigma).mapBranch B) := by
  let F_S := infiniteStrongPictureCanonicalMap hS₀ hS₁ hS₂ hsigma
  let F_U := infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf
  let F_V := infiniteStrongPictureCanonicalMap hV₀ hV₁ hV₂
    (hf.comp hsigma)
  have hrecord : F_V.mapBranch B =
      (CanonicalMap.comp F_U F_S).mapBranch B := by
    cases B with
    | mk k A =>
        change
          (⟨f (sigma k),
            (infiniteEnumCanonicalMap hV₀ hV₁ hV₂
              (k + 1) A).val.truncate (f (sigma k) + 1)⟩ :
                EnumerationBranchNode) =
          ⟨f (sigma k),
            (infiniteEnumCanonicalMap hU₀ hU₁ hU₂
              (sigma (k + 1))
              (infiniteEnumCanonicalMap hS₀ hS₁ hS₂
                (k + 1) A).val).val.truncate (f (sigma k) + 1)⟩
        rw [hEnum (k + 1) A]
  exact hrecord.trans (CanonicalMap.comp_mapBranch F_U F_S B)

theorem infiniteVectorGeometric_relativeMapBranch_comp
    {S₀ S₁ S₂ U₀ U₁ U₂ V₀ V₁ V₂ : Set CoordNode}
    {sigma f : Nat → Nat}
    {rS₀ : EnumNode (sigma 0)} {rS₁ : OneNode (sigma 0)}
    {rS₂ : AuxNode (sigma 0)}
    {rU₀ : EnumNode (f 0)} {rU₁ : OneNode (f 0)}
    {rU₂ : AuxNode (f 0)}
    {rV₀ : EnumNode (f (sigma 0))}
    {rV₁ : OneNode (f (sigma 0))}
    {rV₂ : AuxNode (f (sigma 0))}
    (hS₀ : InfiniteStrongPicture S₀ sigma (.enum (sigma 0) rS₀))
    (hS₁ : InfiniteStrongPicture S₁ sigma (.one (sigma 0) rS₁))
    (hS₂ : InfiniteStrongPicture S₂ sigma (.aux (sigma 0) rS₂))
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) rU₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hV₀ : InfiniteStrongPicture V₀ (fun i => f (sigma i))
      (.enum (f (sigma 0)) rV₀))
    (hV₁ : InfiniteStrongPicture V₁ (fun i => f (sigma i))
      (.one (f (sigma 0)) rV₁))
    (hV₂ : InfiniteStrongPicture V₂ (fun i => f (sigma i))
      (.aux (f (sigma 0)) rV₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f)
    (hEnum : ∀ m (a : EnumNode m),
      (infiniteEnumCanonicalMap hV₀ hV₁ hV₂ m a).val =
        (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma m)
          (infiniteEnumCanonicalMap hS₀ hS₁ hS₂ m a).val).val)
    {n : Nat} (I : EnumNode n)
    (hfixS : ∀ i < n, sigma i = i)
    (hfixU : ∀ i < n, f i = i)
    (hfixV : ∀ i < n, f (sigma i) = i)
    (B : RelativeBranchNode I) :
    (infiniteStrongPictureCanonicalMap hV₀ hV₁ hV₂
        (hf.comp hsigma)).relativeMapBranch_of_fixed_levels
        I hfixV B =
      (infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf)
        .relativeMapBranch_of_fixed_levels I hfixU
          ((infiniteStrongPictureCanonicalMap hS₀ hS₁ hS₂ hsigma)
            .relativeMapBranch_of_fixed_levels I hfixS B) := by
  apply Subtype.ext
  change
    (infiniteStrongPictureCanonicalMap hV₀ hV₁ hV₂
      (hf.comp hsigma)).mapBranch B.val =
    (infiniteStrongPictureCanonicalMap hU₀ hU₁ hU₂ hf).mapBranch
      ((infiniteStrongPictureCanonicalMap hS₀ hS₁ hS₂ hsigma).mapBranch B.val)
  exact infiniteVectorGeometric_mapBranch_comp
    hS₀ hS₁ hS₂ hU₀ hU₁ hU₂ hV₀ hV₁ hV₂
    hsigma hf hEnum B.val

end CoordNode
end ThreeUniformDiaries
