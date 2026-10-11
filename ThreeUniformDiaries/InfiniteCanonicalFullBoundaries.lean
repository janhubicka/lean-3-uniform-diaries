import ThreeUniformDiaries.InfiniteCanonicalLastAuxType
import ThreeUniformDiaries.InfiniteCanonicalEnumRestriction

/-!
# Full selected-boundary identities of genuine infinite canonical maps

The known last-boundary theorems concern nodes at level j+1. Exact
selected restriction lifts those identities to any source level N>j.
Both resulting identities are of COMPLETE target auxiliary or
singleton type nodes, including skipped target coordinates.
-/

namespace ThreeUniformDiaries

namespace OneNode

theorem boundaryAux_truncate_of_lt {N : Nat}
    (a : OneNode N) {j L : Nat} (hjL : j < L) :
    (a.truncate L).boundaryAux j = a.boundaryAux j := by
  apply AuxNode.ext_bits
  funext x
  by_cases hx : x < j
  · simp [OneNode.boundaryAux, OneNode.truncate, hx, hjL]
  · simp [OneNode.boundaryAux, hx]

end OneNode

namespace EnumNode

theorem boundaryOne_truncate_of_lt {N : Nat}
    (a : EnumNode N) {j L : Nat} (hjL : j < L) :
    (a.truncate L).boundaryOne j = a.boundaryOne j := by
  apply OneNode.ext_pairs
  funext x y
  by_cases hv : x < y ∧ y < j
  · simp [EnumNode.boundaryOne, EnumNode.truncate, hv, hjL]
  · simp [EnumNode.boundaryOne, hv]

end EnumNode

namespace CoordNode

theorem infiniteOneCanonicalMap_boundaryAux_compat
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {N j : Nat} (hjN : j < N) (a : OneNode N) :
    (infiniteOneCanonicalMap h₁ h₂ N a).val.boundaryAux (f j) =
      (infiniteAuxCanonicalMap h₂ j (a.boundaryAux j)).val := by
  let W : OneNode (j + 1) := a.truncate (j + 1)
  have htr := infiniteOneCanonicalMap_truncate h₁ h₂ hf
    (j + 1) N (Nat.succ_le_of_lt hjN) a
  have hboundTarget :
      ((infiniteOneCanonicalMap h₁ h₂ N a).val.truncate
        (f (j + 1))).boundaryAux (f j) =
      (infiniteOneCanonicalMap h₁ h₂ N a).val.boundaryAux (f j) :=
    OneNode.boundaryAux_truncate_of_lt _
      (hf (Nat.lt_succ_self j))
  have hboundSource : W.boundaryAux j = a.boundaryAux j :=
    OneNode.boundaryAux_truncate_of_lt a (Nat.lt_succ_self j)
  have hlast := infiniteOneCanonicalMap_lastAuxType h₁ h₂ j W
  rw [hboundSource] at hlast
  calc
    (infiniteOneCanonicalMap h₁ h₂ N a).val.boundaryAux (f j) =
        ((infiniteOneCanonicalMap h₁ h₂ N a).val.truncate
          (f (j + 1))).boundaryAux (f j) := hboundTarget.symm
    _ = (infiniteOneCanonicalMap h₁ h₂ (j + 1) W).val.boundaryAux
          (f j) := by rw [htr]
    _ = (infiniteAuxCanonicalMap h₂ j (a.boundaryAux j)).val := hlast

theorem infiniteEnumCanonicalMap_boundaryOne_compat
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {N j : Nat} (hjN : j < N) (a : EnumNode N) :
    (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val.boundaryOne (f j) =
      (infiniteOneCanonicalMap h₁ h₂ j (a.boundaryOne j)).val := by
  let W : EnumNode (j + 1) := a.truncate (j + 1)
  have htr := infiniteEnumCanonicalMap_truncate h₀ h₁ h₂ hf
    (j + 1) N (Nat.succ_le_of_lt hjN) a
  have hboundTarget :
      ((infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val.truncate
        (f (j + 1))).boundaryOne (f j) =
      (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val.boundaryOne (f j) :=
    EnumNode.boundaryOne_truncate_of_lt _
      (hf (Nat.lt_succ_self j))
  have hboundSource : W.boundaryOne j = a.boundaryOne j :=
    EnumNode.boundaryOne_truncate_of_lt a (Nat.lt_succ_self j)
  have hlast := infiniteEnumCanonicalMap_lastOneType h₀ h₁ h₂ j W
  rw [hboundSource] at hlast
  calc
    (infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val.boundaryOne (f j) =
        ((infiniteEnumCanonicalMap h₀ h₁ h₂ N a).val.truncate
          (f (j + 1))).boundaryOne (f j) := hboundTarget.symm
    _ = (infiniteEnumCanonicalMap h₀ h₁ h₂ (j + 1) W).val.boundaryOne
          (f j) := by rw [htr]
    _ = (infiniteOneCanonicalMap h₁ h₂ j (a.boundaryOne j)).val := hlast

end CoordNode
end ThreeUniformDiaries
