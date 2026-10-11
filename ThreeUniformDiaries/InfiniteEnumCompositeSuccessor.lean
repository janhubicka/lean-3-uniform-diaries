import ThreeUniformDiaries.InfiniteOneCompositeSuccessor

/-!
# Genuine E0 canonical maps preserve successor cones under composition

The entire last singleton-type parameter of the outer image is the
outer E1 canonical image of the inner image's entire last singleton
type. This is true at ALL skipped ambient coordinates, by full selected
boundaryOne compatibility. Combined with exact parent restriction it
gives the E0 successor cone for the pointwise composite.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteEnumCanonicalMap_composite_succ
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
    (i : Nat) (a : EnumNode i) (b : OneNode i) :
    CoordNode.enum (f (sigma i) + 1)
      ((infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma i)
        (infiniteEnumCanonicalMap hS₀ hS₁ hS₂ i a).val).val.succ
        (infiniteOneCanonicalMap hU₁ hU₂ (sigma i)
          (infiniteOneCanonicalMap hS₁ hS₂ i b).val).val) ≤
    CoordNode.enum (f (sigma (i + 1)))
      (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma (i + 1))
        (infiniteEnumCanonicalMap hS₀ hS₁ hS₂ (i + 1)
          (a.succ b)).val).val := by
  let A : EnumNode (sigma (i + 1)) :=
    (infiniteEnumCanonicalMap hS₀ hS₁ hS₂
      (i + 1) (a.succ b)).val
  let B : EnumNode (sigma i) :=
    (infiniteEnumCanonicalMap hS₀ hS₁ hS₂ i a).val
  let D : OneNode (sigma i) :=
    (infiniteOneCanonicalMap hS₁ hS₂ i b).val
  let X : EnumNode (f (sigma (i + 1))) :=
    (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma (i + 1)) A).val
  let P : EnumNode (f (sigma i)) :=
    (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma i) B).val
  let R : OneNode (f (sigma i)) :=
    (infiniteOneCanonicalMap hU₁ hU₂ (sigma i) D).val
  have hsrc : A.truncate (sigma i) = B := by
    have h := infiniteEnumCanonicalMap_truncate hS₀ hS₁ hS₂
      hsigma i (i + 1) (by omega) (a.succ b)
    simpa only [EnumNode.truncate_succ] using h
  have hsrcBoundary : A.boundaryOne (sigma i) = D := by
    have h := infiniteEnumCanonicalMap_lastOneType
      hS₀ hS₁ hS₂ i (a.succ b)
    have hbound :=
      (EnumNode.oneType_self_eq_boundaryOne A (sigma i)).symm
    exact hbound.trans (by
      simpa only [EnumNode.boundaryOne_succ] using h)
  have hparent : X.truncate (f (sigma i)) = P := by
    have h := infiniteEnumCanonicalMap_truncate hU₀ hU₁ hU₂ hf
      (sigma i) (sigma (i + 1))
      (hsigma.monotone (Nat.le_succ i)) A
    simpa only [hsrc] using h
  have htargetBoundary : X.boundaryOne (f (sigma i)) = R := by
    have h := infiniteEnumCanonicalMap_boundaryOne_compat
      hU₀ hU₁ hU₂ hf (hsigma (Nat.lt_succ_self i)) A
    simpa only [hsrcBoundary] using h
  have hcutParent :
      (X.truncate (f (sigma i) + 1)).truncate (f (sigma i)) = P := by
    calc
      (X.truncate (f (sigma i) + 1)).truncate (f (sigma i)) =
        X.truncate (f (sigma i)) :=
          EnumNode.truncate_truncate X (Nat.le_succ _)
      _ = P := hparent
  have hcutBoundary :
      (X.truncate (f (sigma i) + 1)).boundaryOne (f (sigma i)) = R := by
    calc
      (X.truncate (f (sigma i) + 1)).boundaryOne (f (sigma i)) =
        X.boundaryOne (f (sigma i)) :=
          EnumNode.boundaryOne_truncate_of_lt X (Nat.lt_succ_self _)
      _ = R := htargetBoundary
  have hcut : P.succ R = X.truncate (f (sigma i) + 1) := by
    calc
      P.succ R =
        ((X.truncate (f (sigma i) + 1)).truncate (f (sigma i))).succ
          ((X.truncate (f (sigma i) + 1)).boundaryOne (f (sigma i))) := by
            rw [hcutParent, hcutBoundary]
      _ = X.truncate (f (sigma i) + 1) :=
        EnumNode.succ_truncate_boundary _
  refine ⟨?_, ?_⟩
  · change f (sigma i) + 1 ≤ f (sigma (i + 1))
    exact Nat.succ_le_of_lt (hf (hsigma (Nat.lt_succ_self i)))
  · change CoordNode.enum (f (sigma i) + 1)
      (X.truncate (f (sigma i) + 1)) =
      CoordNode.enum (f (sigma i) + 1) (P.succ R)
    rw [hcut]

end CoordNode
end ThreeUniformDiaries
