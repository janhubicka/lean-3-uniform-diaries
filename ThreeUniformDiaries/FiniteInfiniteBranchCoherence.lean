import ThreeUniformDiaries.FiniteInfiniteEnumCanonicalCoherence
import ThreeUniformDiaries.InfiniteCanonicalRecord
import ThreeUniformDiaries.CanonicalBranchSuccessorFormula
import ThreeUniformDiaries.FiniteCanonicalBranchMap

/-!
# Literal finite/infinite canonical branch agreement on every finite vertex

The finite E0/E1/E2 canonical recursions previously proved equal to
their genuine infinite counterparts on strong prefixes. Here their
last-vertex successor combination agrees exactly with the full
canonical branch action used to define the manuscript's F_I^S.

Unlike the earlier Aemb converse, this is uniform over EVERY finite
branch node, not just the distinguished copy g_A(A). It is the
key coherence step for a scalar Milliken finite-approximation colour
to be the restriction of the corresponding infinite K_I action.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- On each finite branch B of source height at most k, the actual
finite F^S formula equals the infinite canonical branch action,
as an equality of the full encoded target enumeration. -/
theorem finitePrefix_branchMap_enumeration_eq_infinite
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) (k : Nat)
    (B : EnumerationBranchNode) (hB : B.last ≤ k) :
    (finiteStrongPicture_branchMap
        (infiniteStrongPicture_finitePrefix_strong h₀ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k)
        B hB).enumeration =
      ((infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf).mapBranch B).enumeration := by
  let F := infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf
  have he :=
    finitePrefix_enumCanonicalMap_eq_infinite h₀ h₁ h₂ hf
      k B.last hB (B.enumeration.truncate B.last)
  have ho :=
    finitePrefix_oneCanonicalMap_eq_infinite h₁ h₂ hf
      k B.last hB (B.enumeration.oneType B.last B.last)
  have hformula := CanonicalMap.mapBranch_succ_formula F B
  change
    (finiteStrongPicture_enumCanonicalMap
        (infiniteStrongPicture_finitePrefix_strong h₀ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k)
        B.last hB (B.enumeration.truncate B.last)).val.succ
      (finiteStrongPicture_oneCanonicalMap
        (infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k)
        B.last hB (B.enumeration.oneType B.last B.last)).val =
      (F.mapBranch B).enumeration
  rw [he, ho]
  change
    (F.mapEnum B.last (B.enumeration.truncate B.last)).succ
      (F.mapOne B.last (B.enumeration.oneType B.last B.last)) =
      (F.mapBranch B).enumeration
  exact hformula.symm

/-- The selected target index in both genuine canonical branch
constructions is also identical. -/
theorem finitePrefix_branchMap_last_eq_infinite
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) (k : Nat)
    (B : EnumerationBranchNode) (hB : B.last ≤ k) :
    (finiteStrongPicture_branchMap
        (infiniteStrongPicture_finitePrefix_strong h₀ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k)
        (infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k)
        B hB).last =
      ((infiniteStrongPictureCanonicalMap h₀ h₁ h₂ hf).mapBranch B).last := rfl

end CoordNode
end ThreeUniformDiaries
