import ThreeUniformDiaries.InfiniteCanonicalSuccessor

/-!
# Exact immediate boundary identities of constructed infinite canonical maps

The three concrete successor-cone inequalities are equivalent to
*equalities* after truncation to the first ambient child level f(i)+1.

For E2 this is the recorded Boolean bit. For E1 it is the image of
the E2 boundary parameter. For E0 it is the image of the E1 boundary
parameter. The equalities hold even when the next SELECTED level
f(i+1) is much later than f(i)+1.

This is a direct geometric interface for cross-coordinate type
compatibility and canonical-map composition. It adds no assumptions
beyond the actual infinite strong-picture axioms.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxCanonicalMap_immediate_prefix
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (i : Nat) (a : AuxNode i) (bit : Bool) :
    (infiniteAuxCanonicalMap hS (i + 1) (a.succ bit)).val.truncate
      (f i + 1) =
    (infiniteAuxCanonicalMap hS i a).val.succ bit := by
  have h := (infiniteAuxCanonicalMap_succ hS i a bit).2
  change CoordNode.aux (f i + 1)
      ((infiniteAuxCanonicalMap hS (i + 1)
        (a.succ bit)).val.truncate (f i + 1)) =
    CoordNode.aux (f i + 1)
      ((infiniteAuxCanonicalMap hS i a).val.succ bit) at h
  injection h

theorem infiniteOneCanonicalMap_immediate_prefix
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (i : Nat) (a : OneNode i) (c : AuxNode i) :
    (infiniteOneCanonicalMap h₁ h₂ (i + 1) (a.succ c)).val.truncate
      (f i + 1) =
    (infiniteOneCanonicalMap h₁ h₂ i a).val.succ
      (infiniteAuxCanonicalMap h₂ i c).val := by
  have h := (infiniteOneCanonicalMap_succ h₁ h₂ i a c).2
  change CoordNode.one (f i + 1)
      ((infiniteOneCanonicalMap h₁ h₂ (i + 1)
        (a.succ c)).val.truncate (f i + 1)) =
    CoordNode.one (f i + 1)
      ((infiniteOneCanonicalMap h₁ h₂ i a).val.succ
        (infiniteAuxCanonicalMap h₂ i c).val) at h
  injection h

theorem infiniteEnumCanonicalMap_immediate_prefix
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (i : Nat) (a : EnumNode i) (b : OneNode i) :
    (infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) (a.succ b)).val.truncate
      (f i + 1) =
    (infiniteEnumCanonicalMap h₀ h₁ h₂ i a).val.succ
      (infiniteOneCanonicalMap h₁ h₂ i b).val := by
  have h := (infiniteEnumCanonicalMap_succ h₀ h₁ h₂ i a b).2
  change CoordNode.enum (f i + 1)
      ((infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1)
        (a.succ b)).val.truncate (f i + 1)) =
    CoordNode.enum (f i + 1)
      ((infiniteEnumCanonicalMap h₀ h₁ h₂ i a).val.succ
        (infiniteOneCanonicalMap h₁ h₂ i b).val) at h
  injection h

end CoordNode
end ThreeUniformDiaries
