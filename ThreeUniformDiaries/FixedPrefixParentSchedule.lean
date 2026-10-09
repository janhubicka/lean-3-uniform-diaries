import ThreeUniformDiaries.SizeFirstFixedPrefix
import ThreeUniformDiaries.SizeFirstParentSchedule
import ThreeUniformDiaries.FixedPrefixGlobalGap

/-!
# The concrete parent schedule for the fixed-prefix K_I embedding

For a nonempty initial segment of size n, source index n+t is added
using the same immediate-prefix parent as the root-based, size-first
enumeration. This connects the source parent theorem to the actual
fixed-prefix countable embedding.
-/

namespace ThreeUniformDiaries
namespace SizeFirstBranchPresentation

variable {n : Nat} {I : EnumNode n} (E : SizeFirstBranchPresentation I)

/-- Parent schedule for the fixed-prefix recursion, obtained by
discarding the first n-1 steps of the global parent schedule. -/
noncomputable def fixedSourceParents (hn : 0 < n) :
    GenericEnumerated3Graph.PrefixParentSchedule n :=
  fun t => ⟨(E.sourceParentSchedule (n + t - 1)).val, by
    have h := (E.sourceParentSchedule (n + t - 1)).isLt
    omega⟩

/-- At every source index beyond the prescribed prefix the two
parent schedules have literally the same chosen parent. -/
theorem fixedSourceParents_at
    (hn : 0 < n) (j : Nat) (hj : n ≤ j) :
    (E.fixedSourceParents hn (j - n)).val =
      (E.sourceParentSchedule (j - 1)).val := by
  change (E.sourceParentSchedule (n + (j - n) - 1)).val =
    (E.sourceParentSchedule (j - 1)).val
  have h : n + (j - n) - 1 = j - 1 := by omega
  rw [h]

/-- Every canonical branch follows the fixed-prefix parent schedule
after the portion that is already fixed pointwise. -/
theorem branchIndex_follows_fixedParents
    (hn : 0 < n)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (t : Nat) (ht : n ≤ E.branchIndex H hI (t + 1)) :
    (E.fixedSourceParents hn
      (E.branchIndex H hI (t + 1) - n)).val =
        E.branchIndex H hI t := by
  rw [E.fixedSourceParents_at hn _ ht]
  exact (E.branchIndex_follows_sourceParents H hI).2 t

/-- The composite of a fixed-prefix inherited embedding and an
original canonical branch fixes each vertex of the original prefix. -/
theorem fixedBranch_initial
    (G : GenericEnumerated3Graph)
    (H : Ordered3Graph Nat)
    (hI : H.initialSegment n = I)
    (hG : G.graph.initialSegment n = I)
    (hn : 0 < n)
    (k : Nat) (hk : k < n) :
    G.fixedInheritedEmbedding E.graph n
      ((E.graph_initialSegment_eq H hI).trans hG.symm)
      (E.fixedSourceParents hn) (E.branchIndex H hI k) = k := by
  rw [E.branchIndex_fixed_prefix H hI k hk]
  exact G.fixedInheritedEmbedding_prefix E.graph n
    ((E.graph_initialSegment_eq H hI).trans hG.symm)
    (E.fixedSourceParents hn) k hk

end SizeFirstBranchPresentation
end ThreeUniformDiaries
