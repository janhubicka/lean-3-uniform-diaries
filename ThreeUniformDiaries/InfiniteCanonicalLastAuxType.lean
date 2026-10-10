import ThreeUniformDiaries.InfiniteCanonicalLastOneType

/-!
# Full boundary auxiliary-type compatibility of infinite canonical maps

The concrete E1 map inserts a new second pair coordinate at each
selected ambient level f(i). Its full auxiliary type over all
ambient vertices below f(i), not merely selected source positions,
is exactly the constructed E2 image of the source boundaryAux i.

Together with the verified E0 last-one-type identity this supplies
both triangular boundary compatibility equations in the manuscript,
without abstract CanonicalMap assumptions.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteOneCanonicalMap_lastAuxType
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (i : Nat) (a : OneNode (i + 1)) :
    (infiniteOneCanonicalMap h₁ h₂ (i + 1) a).val.boundaryAux
      (f i) =
    (infiniteAuxCanonicalMap h₂ i (a.boundaryAux i)).val := by
  have hprefix :=
    infiniteOneCanonicalMap_immediate_prefix
      h₁ h₂ i (a.truncate i) (a.boundaryAux i)
  rw [a.succ_truncate_boundary] at hprefix
  apply AuxNode.ext_bits
  funext x
  by_cases hx : x < f i
  · change
      (if x < f i then
        (infiniteOneCanonicalMap h₁ h₂ (i + 1) a).val.pair
          x (f i) else false) =
      (infiniteAuxCanonicalMap h₂ i (a.boundaryAux i)).val.bit x
    rw [if_pos hx]
    have hb := congrArg
      (fun B : OneNode (f i + 1) => B.pair x (f i)) hprefix
    simpa [OneNode.truncate, OneNode.succ,
      Nat.lt_succ_self] using hb
  · rw [((infiniteOneCanonicalMap h₁ h₂ (i + 1)
        a).val.boundaryAux (f i)).support x (by omega),
      ((infiniteAuxCanonicalMap h₂ i (a.boundaryAux i)).val).support
        x (by omega)]

end CoordNode
end ThreeUniformDiaries
