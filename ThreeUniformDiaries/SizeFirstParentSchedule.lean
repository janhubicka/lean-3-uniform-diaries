import ThreeUniformDiaries.SizeFirstSourceTests
import ThreeUniformDiaries.RelativePrefixClosure

/-!
# Extract a predecessor schedule from a size-first K_I enumeration

The finite inherited-gap construction expects, for the source node
with index k+1, a previously enumerated source index of its immediate
one-vertex-shorter prefix.  Any length-first equivalence supplies
this index: otherwise monotonicity of source lengths gives a contradiction.

We separately allow the length-zero case so the function is total,
but the prefix identity is asserted when the child has positive last
index, exactly as in the intended branch application.
-/

namespace ThreeUniformDiaries
namespace SizeFirstBranchPresentation

variable {n : Nat} {I : EnumNode n} (E : SizeFirstBranchPresentation I)

/-- Predecessor of a non-root node of K_I with the immediately shorter
enumeration length. -/
noncomputable def sourceNodeParent
    (E : SizeFirstBranchPresentation I)
    (A : RelativeBranchNode I) (hA : 0 < A.val.last) : RelativeBranchNode I :=
  relativeBranch_prefix I A (A.val.last - 1) (by omega)

theorem sourceNodeParent_last
    (A : RelativeBranchNode I) (hA : 0 < A.val.last) :
    (E.sourceNodeParent A hA).val.last + 1 = A.val.last := by
  simp [sourceNodeParent]
  omega

/-- A proper prefix necessarily has a smaller enumeration index. -/
theorem sourceNodeParent_index_lt
    (k : Nat)
    (hk : 0 < (E.code (k + 1)).val.last) :
    E.code.symm (E.sourceNodeParent (E.code (k + 1)) hk) < k + 1 := by
  let P := E.sourceNodeParent (E.code (k + 1)) hk
  have hP : P.val.last + 1 = (E.code (k + 1)).val.last :=
    E.sourceNodeParent_last (E.code (k + 1)) hk
  by_contra hnot
  have hle : k + 1 ≤ E.code.symm P := Nat.le_of_not_gt hnot
  have hm := E.length_mono hle
  change (E.code (k + 1)).val.last ≤
    (E.code (E.code.symm P)).val.last at hm
  rw [E.code.apply_symm_apply P] at hm
  omega

/-- The (k+1)-th source node points to its previously enumerated
parent, with a harmless value 0 for an anomalous level-zero node. -/
noncomputable def sourceParentSchedule (k : Nat) : Fin (k + 1) := by
  let A := E.code (k + 1)
  by_cases hA : 0 < A.val.last
  · exact ⟨E.code.symm (E.sourceNodeParent A hA),
      E.sourceNodeParent_index_lt k hA⟩
  · exact ⟨0, by omega⟩

/-- The chosen schedule really names the immediately shorter source
prefix for each child of positive length. -/
theorem sourceParentSchedule_correct
    (k : Nat) (hk : 0 < (E.code (k + 1)).val.last) :
    E.code (E.sourceParentSchedule k).val =
      E.sourceNodeParent (E.code (k + 1)) hk := by
  simp [sourceParentSchedule, hk, sourceNodeParent]

/-- A property of a source branch whose successive nodes use the
designated parent in the size-first source enumeration. -/
def FollowsSourceParents (parent : (k : Nat) → Fin (k + 1))
    (h : Nat → Nat) : Prop :=
  StrictMono h ∧ ∀ t : Nat, (parent (h (t + 1) - 1)).val = h t

/-- Every branch follows the predecessor schedule induced by the
size-first enumeration. -/
theorem branchIndex_follows_sourceParents
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I) :
    FollowsSourceParents E.sourceParentSchedule
      (E.branchIndex H hI) := by
  constructor
  · exact E.branchIndex_strictMono H hI
  · intro t
    let j := E.branchIndex H hI (t + 1)
    have hpos : 0 < j :=
      lt_of_le_of_lt (Nat.zero_le _) (E.branchIndex_strictMono H hI
        (Nat.lt_succ_self t))
    have hstep : (j - 1) + 1 = j := by omega
    have hnode : E.code j = H.relativeBranchNode I hI (t + 1) :=
      E.code_branchIndex H hI (t + 1)
    have hlast : (E.code j).val.last = t + 1 := by
      rw [hnode]
      rfl
    have hp : 0 < (E.code ((j - 1) + 1)).val.last := by
      rw [hstep, hlast]
      omega
    have hsched := E.sourceParentSchedule_correct (j - 1) hp
    have hparent :
        E.sourceNodeParent (E.code j) (by rw [hlast]; omega) =
          H.relativeBranchNode I hI t := by
      apply Subtype.ext
      change (E.code j).val.initialPart ((E.code j).val.last - 1) =
        H.branchNode t
      rw [hnode]
      change (H.branchNode (t + 1)).initialPart ((t + 1) - 1) =
        H.branchNode t
      have ht : (t + 1) - 1 = t := by omega
      rw [ht]
      apply congrArg (fun A : EnumNode (t + 1) =>
        (⟨t, A⟩ : EnumerationBranchNode))
      exact H.initialSegment_truncate (Nat.le_succ (t + 1))
    have hident :
        E.sourceNodeParent (E.code ((j - 1) + 1)) hp =
          H.relativeBranchNode I hI t := by
      simpa [hstep] using hparent
    have hcode :
        E.code (E.sourceParentSchedule (j - 1)).val =
          E.code (E.branchIndex H hI t) := by
      rw [hsched, hident]
      exact (E.code_branchIndex H hI t).symm
    have heq := E.code.injective hcode
    simpa [j] using heq

end SizeFirstBranchPresentation
end ThreeUniformDiaries
