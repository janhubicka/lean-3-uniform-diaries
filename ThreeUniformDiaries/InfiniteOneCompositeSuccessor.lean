import ThreeUniformDiaries.InfiniteCanonicalFullBoundaries

/-!
# Genuine E1 canonical maps preserve successor cones under composition

Compose two actual infinite coupled E1 maps, together with their E2
parameter maps. The composite E1 image of a source successor has:
* its parent equal to the pointwise composite parent;
* its COMPLETE auxiliary boundary at selected index f(sigma i)
  equal to the composite E2 image of the source auxiliary parameter.

Their combined exact one-step prefix yields the required successor
cone, including skipped ambient target indices.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteOneCanonicalMap_composite_succ
    {S₁ S₂ U₁ U₂ : Set CoordNode} {sigma f : Nat → Nat}
    {rS₁ : OneNode (sigma 0)} {rS₂ : AuxNode (sigma 0)}
    {rU₁ : OneNode (f 0)} {rU₂ : AuxNode (f 0)}
    (hS₁ : InfiniteStrongPicture S₁ sigma (.one (sigma 0) rS₁))
    (hS₂ : InfiniteStrongPicture S₂ sigma (.aux (sigma 0) rS₂))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f)
    (i : Nat) (a : OneNode i) (c : AuxNode i) :
    CoordNode.one (f (sigma i) + 1)
      ((infiniteOneCanonicalMap hU₁ hU₂ (sigma i)
        (infiniteOneCanonicalMap hS₁ hS₂ i a).val).val.succ
        (infiniteAuxCanonicalMap hU₂ (sigma i)
          (infiniteAuxCanonicalMap hS₂ i c).val).val) ≤
    CoordNode.one (f (sigma (i + 1)))
      (infiniteOneCanonicalMap hU₁ hU₂ (sigma (i + 1))
        (infiniteOneCanonicalMap hS₁ hS₂ (i + 1) (a.succ c)).val).val := by
  let A : OneNode (sigma (i + 1)) :=
    (infiniteOneCanonicalMap hS₁ hS₂ (i + 1) (a.succ c)).val
  let B : OneNode (sigma i) :=
    (infiniteOneCanonicalMap hS₁ hS₂ i a).val
  let D : AuxNode (sigma i) :=
    (infiniteAuxCanonicalMap hS₂ i c).val
  let X : OneNode (f (sigma (i + 1))) :=
    (infiniteOneCanonicalMap hU₁ hU₂ (sigma (i + 1)) A).val
  let P : OneNode (f (sigma i)) :=
    (infiniteOneCanonicalMap hU₁ hU₂ (sigma i) B).val
  let R : AuxNode (f (sigma i)) :=
    (infiniteAuxCanonicalMap hU₂ (sigma i) D).val
  have hsrc : A.truncate (sigma i) = B := by
    have h := infiniteOneCanonicalMap_truncate hS₁ hS₂ hsigma
      i (i + 1) (by omega) (a.succ c)
    simpa only [OneNode.truncate_succ] using h
  have hsrcBoundary : A.boundaryAux (sigma i) = D := by
    have h := infiniteOneCanonicalMap_lastAuxType hS₁ hS₂
      i (a.succ c)
    simpa only [OneNode.boundaryAux_succ] using h
  have hparent : X.truncate (f (sigma i)) = P := by
    have h := infiniteOneCanonicalMap_truncate hU₁ hU₂ hf
      (sigma i) (sigma (i + 1))
      (hsigma.monotone (Nat.le_succ i)) A
    simpa only [hsrc] using h
  have htargetBoundary : X.boundaryAux (f (sigma i)) = R := by
    have h := infiniteOneCanonicalMap_boundaryAux_compat
      hU₁ hU₂ hf (hsigma (Nat.lt_succ_self i)) A
    simpa only [hsrcBoundary] using h
  have hcutParent :
      (X.truncate (f (sigma i) + 1)).truncate (f (sigma i)) = P := by
    calc
      (X.truncate (f (sigma i) + 1)).truncate (f (sigma i)) =
        X.truncate (f (sigma i)) :=
          OneNode.truncate_truncate X (Nat.le_succ _)
      _ = P := hparent
  have hcutBoundary :
      (X.truncate (f (sigma i) + 1)).boundaryAux (f (sigma i)) = R := by
    calc
      (X.truncate (f (sigma i) + 1)).boundaryAux (f (sigma i)) =
        X.boundaryAux (f (sigma i)) :=
          OneNode.boundaryAux_truncate_of_lt X (Nat.lt_succ_self _)
      _ = R := htargetBoundary
  have hcut : P.succ R = X.truncate (f (sigma i) + 1) := by
    calc
      P.succ R =
        ((X.truncate (f (sigma i) + 1)).truncate (f (sigma i))).succ
          ((X.truncate (f (sigma i) + 1)).boundaryAux (f (sigma i))) := by
            rw [hcutParent, hcutBoundary]
      _ = X.truncate (f (sigma i) + 1) :=
        OneNode.succ_truncate_boundary _
  refine ⟨?_, ?_⟩
  · change f (sigma i) + 1 ≤ f (sigma (i + 1))
    exact Nat.succ_le_of_lt (hf (hsigma (Nat.lt_succ_self i)))
  · change CoordNode.one (f (sigma i) + 1)
      (X.truncate (f (sigma i) + 1)) =
      CoordNode.one (f (sigma i) + 1) (P.succ R)
    rw [hcut]

end CoordNode
end ThreeUniformDiaries
