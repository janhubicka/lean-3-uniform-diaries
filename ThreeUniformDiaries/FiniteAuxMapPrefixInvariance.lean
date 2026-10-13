import ThreeUniformDiaries.FiniteAuxCanonicalMap
import ThreeUniformDiaries.ScalarFiniteCanonicalBranchDecoder
import ThreeUniformDiaries.FiniteStrongLevelCongruence

/-!
# The genuine finite auxiliary canonical map ignores future selected heights

A finite strong picture of height k+1 only uses its selected heights
at indices 0,...,k. The finite auxiliary canonical recursion must
therefore agree for *any two* strictly increasing infinite level
functions f,g which have equal values on this finite initial segment,
provided the underlying finite picture carrier is the same.

The proof does not identify f and g globally. At each source step,
the two previously constructed auxiliary images are the same ambient
type-tree node; applying the Boolean successor to this common node
gives the same immediate ambient cone. The unique selected
representative in that cone must then coincide, because both maps
use the same finite strong carrier S.

This is the lowest-coordinate step needed for the eventual full
finite F_I branch-code invariance under changes to unused tails.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Equality of ambient auxiliary nodes is preserved by appending
the same Boolean boundary bit, even across dependent node indices. -/
private def auxAppendBit (bit : Bool) : CoordNode → CoordNode
  | .aux n a => .aux (n + 1) (a.succ bit)
  | x => zeroChild x

private theorem auxNode_cast {n m : Nat} (h : n = m)
    (a : AuxNode n) :
    (CoordNode.aux n a) =
      CoordNode.aux m (Eq.mp (congrArg AuxNode h) a) := by
  cases h
  rfl

/-- Finite auxiliary canonical image nodes are independent of
all selected-height data above the last finite source level. -/
theorem finiteAuxCanonicalMap_eq_of_prefix_heights
    {S : Set CoordNode} {f g : Nat → Nat} {k : Nat}
    {rf : AuxNode (f 0)} {rg : AuxNode (g 0)}
    (hF : FiniteStrongPicture S f k (.aux (f 0) rf))
    (hG : FiniteStrongPicture S g k (.aux (g 0) rg))
    (heights : ∀ i : Nat, i ≤ k → f i = g i) :
    ∀ (i : Nat) (hi : i ≤ k) (a : AuxNode i),
      (CoordNode.aux (f i)
        (finiteStrongPicture_auxCanonicalMap hF i hi a).val) =
      (CoordNode.aux (g i)
        (finiteStrongPicture_auxCanonicalMap hG i hi a).val) := by
  intro i
  induction i with
  | zero =>
      intro hi a
      change (CoordNode.aux (f 0) rf) =
        (CoordNode.aux (g 0) rg)
      exact ATRFiniteDecoder.finiteStrongPicture_root_unique hF hG
  | succ i ih =>
      intro hi a
      have hik : i < k := by omega
      have hi0 : i ≤ k := by omega
      let bit : Bool := a.bit i
      let prevF :=
        finiteStrongPicture_auxCanonicalMap hF i hi0 (a.truncate i)
      let prevG :=
        finiteStrongPicture_auxCanonicalMap hG i hi0 (a.truncate i)
      let curF := finiteStrongPicture_auxCanonicalMap hF (i + 1) hi a
      let curG := finiteStrongPicture_auxCanonicalMap hG (i + 1) hi a
      have hprev :
          (CoordNode.aux (f i) prevF.val) =
          (CoordNode.aux (g i) prevG.val) := ih hi0 (a.truncate i)
      have hchild :
          (CoordNode.aux (f i + 1) (prevF.val.succ bit)) =
          (CoordNode.aux (g i + 1) (prevG.val.succ bit)) := by
        exact congrArg (auxAppendBit bit) hprev
      have hspecF :
          CoordNode.aux (f (i + 1)) curF.val ∈ S ∧
          CoordNode.aux (f i + 1) (prevF.val.succ bit) ≤
            CoordNode.aux (f (i + 1)) curF.val := by
        exact finiteStrongPicture_auxStep_spec hF
          i hik prevF.val prevF.property bit
      have hspecG :
          CoordNode.aux (g (i + 1)) curG.val ∈ S ∧
          CoordNode.aux (g i + 1) (prevG.val.succ bit) ≤
            CoordNode.aux (g (i + 1)) curG.val := by
        exact finiteStrongPicture_auxStep_spec hG
          i hik prevG.val prevG.property bit
      have hheight : g (i + 1) = f (i + 1) :=
        (heights (i + 1) hi).symm
      let q : AuxNode (f (i + 1)) :=
        Eq.mp (congrArg AuxNode hheight) curG.val
      have hqNode :
          CoordNode.aux (g (i + 1)) curG.val =
          CoordNode.aux (f (i + 1)) q := by
        exact auxNode_cast hheight curG.val
      have hqMem : CoordNode.aux (f (i + 1)) q ∈ S := by
        rw [← hqNode]
        exact hspecG.1
      have hqCone :
          CoordNode.aux (f i + 1) (prevF.val.succ bit) ≤
            CoordNode.aux (f (i + 1)) q := by
        rw [← hqNode, hchild]
        exact hspecG.2
      obtain ⟨w, _, hunique⟩ :=
        finiteStrongPicture_aux_lift hF i hik
          prevF.val prevF.property bit
      have hFVal : curF.val = w :=
        hunique curF.val hspecF
      have hGVal : q = w :=
        hunique q ⟨hqMem, hqCone⟩
      calc
        (CoordNode.aux (f (i + 1)) curF.val) =
          CoordNode.aux (f (i + 1)) q := by
            rw [hFVal, hGVal]
        _ = CoordNode.aux (g (i + 1)) curG.val :=
          hqNode.symm

end CoordNode
end ThreeUniformDiaries
