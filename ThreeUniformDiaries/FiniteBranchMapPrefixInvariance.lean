import ThreeUniformDiaries.FiniteCoupledMapPrefixInvariance
import ThreeUniformDiaries.FiniteCanonicalBranchMap

/-!
# Full F_I branch code is insensitive to unused future selected levels

The canonical E2/E1/E0 finite type maps were proved independent of
changes to their common selected-level function above source height k.
Now assemble the dependent last-index and enumeration fields of the
actual finite F_I branch map. The result holds on EVERY universal
enumeration branch B with B.last ≤ k, not merely on g_A(A).

Consequently the finite F_I colouring of a genuine scalar Milliken
approximation depends only on its actual finite node carrier and
intrinsic finite source heights, never on an arbitrary infinite
realizer's unused future source levels.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Assemble the last-vertex successor from ambient type nodes.
The use of `Option` avoids inventing a fake branch when the inputs
are not a valid E0/E1 pair at one common ambient height. -/
private def branchFromTypeNodes :
    CoordNode → CoordNode → Option EnumerationBranchNode
  | .enum n a, .one m b =>
      if h : n = m then
        some ⟨n, a.succ (h.symm ▸ b)⟩
      else none
  | _, _ => none

/-- The full dependent F_I branch vertices computed from two genuine
finite three-coordinate strong pictures agree whenever their carriers
and the first k+1 selected ambient heights agree. -/
theorem finiteStrongPicture_branchMap_eq_of_prefix_heights
    {S₀ S₁ S₂ : Set CoordNode} {f g : Nat → Nat} {k : Nat}
    {rf₀ : EnumNode (f 0)} {rf₁ : OneNode (f 0)}
    {rf₂ : AuxNode (f 0)}
    {rg₀ : EnumNode (g 0)} {rg₁ : OneNode (g 0)}
    {rg₂ : AuxNode (g 0)}
    (hF₀ : FiniteStrongPicture S₀ f k (.enum (f 0) rf₀))
    (hF₁ : FiniteStrongPicture S₁ f k (.one (f 0) rf₁))
    (hF₂ : FiniteStrongPicture S₂ f k (.aux (f 0) rf₂))
    (hG₀ : FiniteStrongPicture S₀ g k (.enum (g 0) rg₀))
    (hG₁ : FiniteStrongPicture S₁ g k (.one (g 0) rg₁))
    (hG₂ : FiniteStrongPicture S₂ g k (.aux (g 0) rg₂))
    (heights : ∀ i : Nat, i ≤ k → f i = g i)
    (B : EnumerationBranchNode) (hB : B.last ≤ k) :
    finiteStrongPicture_branchMap hF₀ hF₁ hF₂ B hB =
      finiteStrongPicture_branchMap hG₀ hG₁ hG₂ B hB := by
  let enumF :=
    finiteStrongPicture_enumCanonicalMap hF₀ hF₁ hF₂
      B.last hB (B.enumeration.truncate B.last)
  let enumG :=
    finiteStrongPicture_enumCanonicalMap hG₀ hG₁ hG₂
      B.last hB (B.enumeration.truncate B.last)
  let oneF :=
    finiteStrongPicture_oneCanonicalMap hF₁ hF₂
      B.last hB (B.enumeration.oneType B.last B.last)
  let oneG :=
    finiteStrongPicture_oneCanonicalMap hG₁ hG₂
      B.last hB (B.enumeration.oneType B.last B.last)
  have he :
      CoordNode.enum (f B.last) enumF.val =
        CoordNode.enum (g B.last) enumG.val :=
    finiteEnumCanonicalMap_eq_of_prefix_heights
      hF₀ hF₁ hF₂ hG₀ hG₁ hG₂
      heights B.last hB (B.enumeration.truncate B.last)
  have ho :
      CoordNode.one (f B.last) oneF.val =
        CoordNode.one (g B.last) oneG.val :=
    finiteOneCanonicalMap_eq_of_prefix_heights
      hF₁ hF₂ hG₁ hG₂
      heights B.last hB (B.enumeration.oneType B.last B.last)
  have hfun :
      branchFromTypeNodes
        (CoordNode.enum (f B.last) enumF.val)
        (CoordNode.one (f B.last) oneF.val) =
      branchFromTypeNodes
        (CoordNode.enum (g B.last) enumG.val)
        (CoordNode.one (g B.last) oneG.val) :=
    congrArg₂ branchFromTypeNodes he ho
  have hsome : some (finiteStrongPicture_branchMap hF₀ hF₁ hF₂ B hB) =
      some (finiteStrongPicture_branchMap hG₀ hG₁ hG₂ B hB) := by
    calc
      some (finiteStrongPicture_branchMap hF₀ hF₁ hF₂ B hB) =
          branchFromTypeNodes
            (CoordNode.enum (f B.last) enumF.val)
            (CoordNode.one (f B.last) oneF.val) := by
          rfl
      _ = branchFromTypeNodes
            (CoordNode.enum (g B.last) enumG.val)
            (CoordNode.one (g B.last) oneG.val) := hfun
      _ = some (finiteStrongPicture_branchMap hG₀ hG₁ hG₂ B hB) := by
          rfl
  exact Option.some.inj hsome

end CoordNode
end ThreeUniformDiaries
