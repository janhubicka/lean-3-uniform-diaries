import ThreeUniformDiaries.InfiniteCanonicalLastOneType
import ThreeUniformDiaries.InfiniteCanonicalAuxOneRestriction
import ThreeUniformDiaries.TypeNodePrefix

/-!
# Full singleton-type compatibility of the actual infinite canonical maps

The last-vertex E0/E1 boundary identity gives the singleton type of
a newly selected vertex at its OWN cut. For any earlier source cut
l <= v, selected-level truncation of the concrete E1 canonical map
then gives the singleton type at target cut f(l). Similarly, E0
selected-truncation transports the answer from any later finite
source enumeration down to the moment vertex v was introduced.

The result is EXACTLY CanonicalMap.oneType_compat for every finite
enumerated source and every l <= v < N, including all skipped ambient
target indices. No abstract compatibility axiom is assumed.
-/

namespace ThreeUniformDiaries

namespace EnumNode

/-- Restricting the underlying hypergraph beyond the type vertex
does not change its one-type over any chosen cut. -/
theorem oneType_of_source_truncate
    {N : Nat} (H : EnumNode N)
    (t l v : Nat) (hvt : v < t) :
    (H.truncate t).oneType l v = H.oneType l v := by
  apply OneNode.ext_pairs
  funext x y
  by_cases hyl : y < l
  · simp [EnumNode.oneType, EnumNode.truncate, hyl, hvt]
  · simp [EnumNode.oneType, hyl]

/-- The one-type at the last selected vertex is the last boundary
parameter of the corresponding source enumeration prefix. -/
theorem truncate_next_boundaryOne_eq_oneType
    {N : Nat} (H : EnumNode N) (v : Nat) :
    (H.truncate (v + 1)).boundaryOne v = H.oneType v v := by
  apply OneNode.ext_pairs
  funext x y
  by_cases hvalid : x < y ∧ y < v
  · simp [EnumNode.boundaryOne, EnumNode.oneType,
      EnumNode.truncate, hvalid, Nat.lt_succ_self v]
  · rw [((H.truncate (v + 1)).boundaryOne v).support x y hvalid,
      (H.oneType v v).support x y hvalid]

end EnumNode

namespace CoordNode

/-- Actual infinite E1 images equal the full one-types formed in
actual infinite E0 images, at ALL ambient coordinates below f(l). -/
theorem infiniteCanonicalMap_oneType_compat
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {N l v : Nat} (H : EnumNode N)
    (hlv : l ≤ v) (hvN : v < N) :
    (infiniteOneCanonicalMap h₁ h₂ l (H.oneType l v)).val =
    (infiniteEnumCanonicalMap h₀ h₁ h₂ N H).val.oneType
      (f l) (f v) := by
  let B := (infiniteEnumCanonicalMap h₀ h₁ h₂ N H).val
  have hvl : f l ≤ f v := hf.monotone hlv
  have hvplus : v + 1 ≤ N := by omega
  have hBcut :=
    infiniteEnumCanonicalMap_truncate h₀ h₁ h₂ hf
      (v + 1) N hvplus H
  have hlast :=
    infiniteEnumCanonicalMap_lastOneType h₀ h₁ h₂ v
      (H.truncate (v + 1))
  have hsource :
      (H.truncate (v + 1)).boundaryOne v = H.oneType v v :=
    H.truncate_next_boundaryOne_eq_oneType v
  have htarget :
      B.oneType (f v) (f v) =
      (infiniteOneCanonicalMap h₁ h₂ v (H.oneType v v)).val := by
    calc
      B.oneType (f v) (f v) =
          (B.truncate (f (v + 1))).oneType (f v) (f v) :=
        (B.oneType_of_source_truncate
          (f (v + 1)) (f v) (f v)
          (hf (Nat.lt_succ_self v))).symm
      _ = (infiniteEnumCanonicalMap h₀ h₁ h₂ (v + 1)
            (H.truncate (v + 1))).val.oneType (f v) (f v) := by
          rw [hBcut]
      _ = (infiniteOneCanonicalMap h₁ h₂ v
            ((H.truncate (v + 1)).boundaryOne v)).val := hlast
      _ = (infiniteOneCanonicalMap h₁ h₂ v (H.oneType v v)).val := by
          rw [hsource]
  have hOneCut :=
    infiniteOneCanonicalMap_truncate h₁ h₂ hf l v hlv
      (H.oneType v v)
  have hSrcCut := H.oneType_truncate (u := v) hlv
  have hDstCut := B.oneType_truncate (u := f v) hvl
  calc
    (infiniteOneCanonicalMap h₁ h₂ l (H.oneType l v)).val =
      (infiniteOneCanonicalMap h₁ h₂ l
        ((H.oneType v v).truncate l)).val := by rw [hSrcCut]
    _ = (infiniteOneCanonicalMap h₁ h₂ v
          (H.oneType v v)).val.truncate (f l) := hOneCut.symm
    _ = (B.oneType (f v) (f v)).truncate (f l) := by rw [htarget]
    _ = B.oneType (f l) (f v) := hDstCut

end CoordNode
end ThreeUniformDiaries
