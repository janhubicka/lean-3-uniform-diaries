import ThreeUniformDiaries.InfiniteCanonicalSelectedAuxBits

/-!
# The composition of genuine E2 maps follows the correct successor cone

Given two genuine geometric auxiliary canonical maps, the first at
levels sigma and the second at levels f, their pointwise composite
preserves the complete parent node and inserts the original successor
bit at selected coordinate f(sigma i).

Consequently the composite follows the actual successor cone of
a canonical map on the composed level map f ∘ sigma. This is
precisely the missing cone premise of the independent geometric E2
uniqueness theorem.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxCanonicalMap_composite_succ
    {S U : Set CoordNode} {f sigma : Nat → Nat}
    {rS : AuxNode (sigma 0)} {rU : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S sigma (.aux (sigma 0) rS))
    (hU : InfiniteStrongPicture U f (.aux (f 0) rU))
    (hsigma : StrictMono sigma) (hf : StrictMono f)
    (i : Nat) (a : AuxNode i) (bit : Bool) :
    CoordNode.aux (f (sigma i) + 1)
      ((infiniteAuxCanonicalMap hU (sigma i)
        (infiniteAuxCanonicalMap hS i a).val).val.succ bit) ≤
    CoordNode.aux (f (sigma (i + 1)))
      (infiniteAuxCanonicalMap hU (sigma (i + 1))
        (infiniteAuxCanonicalMap hS (i + 1) (a.succ bit)).val).val := by
  let A : AuxNode (sigma (i + 1)) :=
    (infiniteAuxCanonicalMap hS (i + 1) (a.succ bit)).val
  let B : AuxNode (sigma i) :=
    (infiniteAuxCanonicalMap hS i a).val
  let X : AuxNode (f (sigma (i + 1))) :=
    (infiniteAuxCanonicalMap hU (sigma (i + 1)) A).val
  let P : AuxNode (f (sigma i)) :=
    (infiniteAuxCanonicalMap hU (sigma i) B).val
  have hsrc : A.truncate (sigma i) = B := by
    have h := infiniteAuxCanonicalMap_truncate hS hsigma
      i (i + 1) (by omega) (a.succ bit)
    simpa only [AuxNode.truncate_succ] using h
  have hparent : X.truncate (f (sigma i)) = P := by
    have h := infiniteAuxCanonicalMap_truncate hU hf
      (sigma i) (sigma (i + 1))
      (hsigma.monotone (Nat.le_succ i)) A
    simpa only [hsrc] using h
  have hsourceBit : A.bit (sigma i) = bit := by
    have h := infiniteAuxCanonicalMap_newBit hS i (a.succ bit)
    simpa only [AuxNode.succ_new] using h
  have htargetBit : X.bit (f (sigma i)) = bit := by
    have h := infiniteAuxCanonicalMap_selectedBit hU hf
      (sigma (i + 1)) (sigma i)
      (hsigma (Nat.lt_succ_self i)) A
    exact h.trans hsourceBit
  have hCutParent :
      (X.truncate (f (sigma i) + 1)).truncate (f (sigma i)) = P := by
    calc
      (X.truncate (f (sigma i) + 1)).truncate (f (sigma i)) =
          X.truncate (f (sigma i)) :=
        AuxNode.truncate_truncate X (Nat.le_succ _)
      _ = P := hparent
  have hCutBit :
      (X.truncate (f (sigma i) + 1)).bit (f (sigma i)) = bit := by
    simpa [AuxNode.truncate, Nat.lt_succ_self] using htargetBit
  have hCutEq :
      P.succ bit = X.truncate (f (sigma i) + 1) := by
    calc
      P.succ bit =
          ((X.truncate (f (sigma i) + 1)).truncate
            (f (sigma i))).succ
            ((X.truncate (f (sigma i) + 1)).bit
              (f (sigma i))) := by rw [hCutParent, hCutBit]
      _ = X.truncate (f (sigma i) + 1) :=
        AuxNode.succ_truncate_new _
  refine ⟨?_, ?_⟩
  · change f (sigma i) + 1 ≤ f (sigma (i + 1))
    exact Nat.succ_le_of_lt (hf (hsigma (Nat.lt_succ_self i)))
  · change CoordNode.aux (f (sigma i) + 1)
      (X.truncate (f (sigma i) + 1)) =
      CoordNode.aux (f (sigma i) + 1) (P.succ bit)
    rw [hCutEq]

end CoordNode
end ThreeUniformDiaries
