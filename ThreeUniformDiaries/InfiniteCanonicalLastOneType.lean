import ThreeUniformDiaries.InfiniteCanonicalImmediatePrefixes

/-!
# Last-vertex one-type compatibility of actual infinite canonical maps

The constructed E0 image of a finite enumeration has a genuinely
new vertex at each selected target level f(i). The complete 1-type
of that new vertex over the preceding target cut f(i) is LITERALLY
the image under the constructed E1 canonical map of the source
last-vertex boundaryOne i.

This is stronger than preservation of only pairs at the selected
indices: it covers every ambient pair below f(i), including skipped
target vertices. It is the first cross-coordinate compatibility
theorem required to realize the abstract CanonicalMap record from
the actual geometric infinite strong subtree.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteEnumCanonicalMap_lastOneType
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (i : Nat) (H : EnumNode (i + 1)) :
    (infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) H).val.oneType
      (f i) (f i) =
    (infiniteOneCanonicalMap h₁ h₂ i (H.boundaryOne i)).val := by
  have hprefix :=
    infiniteEnumCanonicalMap_immediate_prefix
      h₀ h₁ h₂ i (H.truncate i) (H.boundaryOne i)
  rw [H.succ_truncate_boundary] at hprefix
  apply OneNode.ext_pairs
  funext x y
  by_cases hy : y < f i
  · change (if y < f i then
        (infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) H).val.triple
          x y (f i) else false) =
      (infiniteOneCanonicalMap h₁ h₂ i (H.boundaryOne i)).val.pair x y
    rw [if_pos hy]
    have hb := congrArg
      (fun B : EnumNode (f i + 1) => B.triple x y (f i)) hprefix
    simpa [EnumNode.truncate, EnumNode.succ,
      Nat.lt_succ_self] using hb
  · have hbad : ¬ (x < y ∧ y < f i) := by
      intro h
      exact hy h.2
    rw [((infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1)
       H).val.oneType (f i) (f i)).support x y hbad,
      ((infiniteOneCanonicalMap h₁ h₂ i (H.boundaryOne i)).val).support
        x y hbad]

end CoordNode
end ThreeUniformDiaries
