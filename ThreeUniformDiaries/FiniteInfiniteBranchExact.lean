import ThreeUniformDiaries.FiniteInfiniteBranchCoherence
import ThreeUniformDiaries.FiniteCanonicalBranchMap
import ThreeUniformDiaries.InfiniteCanonicalRecord

/-!
# The complete finite F_I branch agrees with the infinite canonical map

The finite/infinite coherence proof already established equality
of the last target index and the resulting target enumeration
separately, for every source branch, not only for a selected A-branch.

These are dependent fields of EnumerationBranchNode: its enumeration
has length last+1. We explicitly assemble the two verified field
identities into equality of the WHOLE branch node, eliminating the
last dependency-cast gap in passing finite F_I calculations to the
infinite geometric canonical map.

No branching bound or heterogeneous Milliken input is used.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Extensionality for the dependent last-vertex enumeration record,
with explicit heterogeneous equality when the indices differ. -/
private theorem enumerationBranchNode_ext
    (B C : EnumerationBranchNode)
    (hl : B.last = C.last)
    (he : HEq B.enumeration C.enumeration) :
    B = C := by
  cases B with
  | mk i a =>
      cases C with
      | mk j b =>
          cases hl
          cases he
          rfl

/-- The actual finite E0/E1/E2 last-vertex successor formula
is EXACTLY the full infinite canonical map on each branch vertex,
whenever the finite pictures are the first k+1 selected levels. -/
theorem finitePrefix_branchMap_eq_infinite
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) (k : Nat)
    (B : EnumerationBranchNode) (hB : B.last ≤ k) :
    finiteStrongPicture_branchMap
      (infiniteStrongPicture_finitePrefix_strong h₀ hf rfl k)
      (infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k)
      (infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k)
      B hB =
      (infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf).mapBranch B := by
  have hlast :=
    finitePrefix_branchMap_last_eq_infinite
      h₀ h₁ h₂ hf k B hB
  have henum :=
    finitePrefix_branchMap_enumeration_eq_infinite
      h₀ h₁ h₂ hf k B hB
  apply enumerationBranchNode_ext _ _ hlast
  cases henum
  rfl

end CoordNode
end ThreeUniformDiaries
