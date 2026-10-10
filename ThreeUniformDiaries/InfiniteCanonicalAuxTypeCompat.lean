import ThreeUniformDiaries.InfiniteCanonicalOneTypeCompat
import ThreeUniformDiaries.InfiniteCanonicalLastAuxType

/-!
# Full auxiliary-type compatibility of concrete infinite canonical maps

The auxiliary type of u < v is the boundary auxiliary type of
the singleton type of v over any cut beyond u.  The already verified
full E1 singleton-type compatibility and E1/E2 last-boundary identity
therefore give the E2 auxiliary-type compatibility at the cut u.
Selected-level truncation propagates it to every earlier cut l <= u.

Crucially, the equality holds at ALL target ambient coordinates below
f(l), not only at the selected indices; no abstract CanonicalMap
compatibility field is assumed.
-/

namespace ThreeUniformDiaries

namespace EnumNode

/-- The auxiliary type of (u,v) is the boundary of the singleton type
of v at u, provided the singleton cut includes u. -/
theorem oneType_boundaryAux_eq_auxType_of_lt
    {N : Nat} (H : EnumNode N) (cut u v : Nat) (huc : u < cut) :
    (H.oneType cut v).boundaryAux u = H.auxType u u v := by
  apply AuxNode.ext_bits
  funext x
  by_cases hx : x < u
  · simp [OneNode.boundaryAux, EnumNode.oneType,
      EnumNode.auxType, hx, huc]
  · have hxu : u ≤ x := Nat.le_of_not_gt hx
    rw [((H.oneType cut v).boundaryAux u).support x hxu,
      (H.auxType u u v).support x hxu]

end EnumNode

namespace CoordNode

/-- The genuine infinite E2 map takes a source auxiliary type over l
to the FULL auxiliary type in the genuine E0 image over f(l).
All skipped target coordinates are included. -/
theorem infiniteCanonicalMap_auxType_compat
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {N l u v : Nat} (H : EnumNode N)
    (hlu : l ≤ u) (huv : u < v) (hvN : v < N) :
    (infiniteAuxCanonicalMap h₂ l (H.auxType l u v)).val =
    (infiniteEnumCanonicalMap h₀ h₁ h₂ N H).val.auxType
      (f l) (f u) (f v) := by
  let B := (infiniteEnumCanonicalMap h₀ h₁ h₂ N H).val
  have hfuc : f u < f (u + 1) := hf (Nat.lt_succ_self u)
  have hsource :
      (H.oneType (u + 1) v).boundaryAux u = H.auxType u u v :=
    H.oneType_boundaryAux_eq_auxType_of_lt
      (u + 1) u v (Nat.lt_succ_self u)
  have hOne :=
    infiniteCanonicalMap_oneType_compat h₀ h₁ h₂ hf H
      (show u + 1 ≤ v by omega) hvN
  have hlast :=
    infiniteOneCanonicalMap_lastAuxType h₁ h₂ u
      (H.oneType (u + 1) v)
  have htarget :
      (infiniteAuxCanonicalMap h₂ u (H.auxType u u v)).val =
        B.auxType (f u) (f u) (f v) := by
    calc
      (infiniteAuxCanonicalMap h₂ u (H.auxType u u v)).val =
          (infiniteAuxCanonicalMap h₂ u
            ((H.oneType (u + 1) v).boundaryAux u)).val := by
              rw [hsource]
      _ = (infiniteOneCanonicalMap h₁ h₂ (u + 1)
            (H.oneType (u + 1) v)).val.boundaryAux (f u) :=
          hlast.symm
      _ = (B.oneType (f (u + 1)) (f v)).boundaryAux (f u) := by
          rw [hOne]
      _ = B.auxType (f u) (f u) (f v) :=
          B.oneType_boundaryAux_eq_auxType_of_lt
            (f (u + 1)) (f u) (f v) hfuc
  have hAuxCut :=
    infiniteAuxCanonicalMap_truncate h₂ hf l u hlu (H.auxType u u v)
  have hSrcCut :
      (H.auxType u u v).truncate l = H.auxType l u v :=
    H.auxType_truncate (l := u) (k := l) (u := u) (v := v) hlu
  have hDstCut :
      (B.auxType (f u) (f u) (f v)).truncate (f l) =
        B.auxType (f l) (f u) (f v) :=
    B.auxType_truncate (l := f u) (k := f l)
      (u := f u) (v := f v) (hf.monotone hlu)
  calc
    (infiniteAuxCanonicalMap h₂ l (H.auxType l u v)).val =
        (infiniteAuxCanonicalMap h₂ l
          ((H.auxType u u v).truncate l)).val := by rw [hSrcCut]
    _ = (infiniteAuxCanonicalMap h₂ u
          (H.auxType u u v)).val.truncate (f l) := hAuxCut.symm
    _ = (B.auxType (f u) (f u) (f v)).truncate (f l) := by
          rw [htarget]
    _ = B.auxType (f l) (f u) (f v) := hDstCut

end CoordNode
end ThreeUniformDiaries
