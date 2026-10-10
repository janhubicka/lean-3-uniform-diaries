import ThreeUniformDiaries.InfiniteCanonicalRecord
import ThreeUniformDiaries.CanonicalExactMeets

/-!
# Exact capped meets for the actual infinite canonical enumeration map

The manuscript requires the selected vertex map of a geometric infinite
strong vector subtree to preserve singleton and auxiliary capped meets
literally, not merely their agreement relations at selected source cuts.

The abstract exact-meet lemmas have already been formalized for
CanonicalMap. We now instantiate them with the genuine infinite maps:
this is valid because *all* CanonicalMap fields have been derived,
including the ambient nonselected auxiliary-type identities.

This proves exact one-/aux-meet preservation in every finite source
prefix. Passing to a countable union and identifying the infinite
K_I branch map remains separate.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteCanonicalMap_oneMeetLevel_preserved
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {N : Nat} (H : EnumNode N)
    (u v : Nat) (hu : u < N) (hv : v < N) :
    ((infiniteEnumCanonicalMap h₀ h₁ h₂ N H).val.toOrdered3Graph).oneMeetLevel
      (f u) (f v) =
      f (H.toOrdered3Graph.oneMeetLevel u v) := by
  exact (CanonicalMap.oneMeetLevel_preserved_on_finite
    (infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf)
    H u v hu hv)

theorem infiniteCanonicalMap_auxMeetLevel_preserved
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {N : Nat} (H : EnumNode N)
    (u₀ u₁ v₀ v₁ : Nat)
    (hu : u₀ < u₁) (huN : u₁ < N)
    (hv : v₀ < v₁) (hvN : v₁ < N) :
    ((infiniteEnumCanonicalMap h₀ h₁ h₂ N H).val.toOrdered3Graph).auxMeetLevel
      (f u₀) (f u₁) (f v₀) (f v₁) =
      f (H.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁) := by
  exact (CanonicalMap.auxMeetLevel_preserved_on_finite
    (infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf)
    H u₀ u₁ v₀ v₁ hu huN hv hvN)

end CoordNode
end ThreeUniformDiaries
