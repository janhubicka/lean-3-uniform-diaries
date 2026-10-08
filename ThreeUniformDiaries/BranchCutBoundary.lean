import ThreeUniformDiaries.BranchTypeAgreement

/-!
# The last selected level in branch-type comparisons

The manuscript compares *target positions* below the image of a
branch vertex, whereas BranchTypeAgreement.lean compares source
enumeration *lengths* strictly below the corresponding original cut.
A length-first enumeration can place nodes of the same length as the
branch vertex before that vertex. These are harmless: if they are
not the branch vertex, they cannot form a hyperedge with a later
vertex of that branch.

This file closes precisely this boundary case for both singleton and
auxiliary comparisons, uniformly over relative K_I.
-/

namespace ThreeUniformDiaries

namespace EnumerationBranchNode

/-- An enumeration node at length w+1 whose finite hypergraph equals
the w+1 prefix of H is the actual w-th branch node. -/
theorem eq_branchNode_of_prefix
    (H : Ordered3Graph Nat) (A : EnumerationBranchNode) (w : Nat)
    (hw : A.last = w)
    (hA : A.enumeration = H.initialSegment (A.last + 1)) :
    A = H.branchNode w := by
  cases A with
  | mk k E =>
      change k = w at hw
      subst k
      change E = H.initialSegment (w + 1) at hA
      cases hA
      rfl

end EnumerationBranchNode

namespace Ordered3Graph

/-- A node at the same length as H|_(w+1), but different from it,
cannot participate as a middle node in a later branch edge. -/
theorem no_branch_edge_wrong_middle
    (H : Ordered3Graph Nat) (a b : EnumerationBranchNode)
    (w u : Nat) (hb : b.last = w)
    (hwrong : b ≠ H.branchNode w) :
    ¬ universalBranchGraph.edge a b (H.branchNode u) := by
  intro hedge
  have hbu : b.last < u := hedge.2.1
  have hprefix :
      (H.initialSegment (u + 1)).truncate (b.last + 1) =
        b.enumeration := hedge.2.2.2.1
  have hfull :
      b.enumeration = H.initialSegment (b.last + 1) := by
    exact hprefix.symm.trans
      (H.initialSegment_truncate (Nat.succ_le_succ hbu.le))
  exact hwrong (b.eq_branchNode_of_prefix H w hb hfull)

/-- Likewise, a wrong same-length node cannot be an auxiliary test
vertex in an edge through two later vertices of one branch. -/
theorem no_branch_edge_wrong_first
    (H : Ordered3Graph Nat) (a : EnumerationBranchNode)
    (w u v : Nat) (ha : a.last = w)
    (hwrong : a ≠ H.branchNode w) :
    ¬ universalBranchGraph.edge a (H.branchNode u) (H.branchNode v) := by
  intro hedge
  have hau : a.last < u := hedge.1
  have hprefix :
      (H.initialSegment (u + 1)).truncate (a.last + 1) =
        a.enumeration := hedge.2.2.1
  have hfull :
      a.enumeration = H.initialSegment (a.last + 1) := by
    exact hprefix.symm.trans
      (H.initialSegment_truncate (Nat.succ_le_succ hau.le))
  exact hwrong (a.eq_branchNode_of_prefix H w ha hfull)

/-- One-type agreement is preserved by all candidate tests at levels
at most w, except the branch cut vertex itself (which cannot lie
strictly before its image). -/
theorem relativeBranch_sameOneType_at_boundary
    (H : Ordered3Graph Nat) {n : Nat}
    (I : EnumNode n) (hI : H.initialSegment n = I)
    (w u v : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hsame : H.SameOneTypeBelow w u v)
    (a b : RelativeBranchNode I)
    (hab : a.val.last < b.val.last)
    (hb : b.val.last ≤ w)
    (hwrong : b.val.last = w → b.val ≠ H.branchNode w) :
    (relativeBranchGraph I).edge a b (H.relativeBranchNode I hI u) ↔
      (relativeBranchGraph I).edge a b (H.relativeBranchNode I hI v) := by
  change universalBranchGraph.edge a.val b.val (H.branchNode u) ↔
    universalBranchGraph.edge a.val b.val (H.branchNode v)
  by_cases hbw : b.val.last < w
  · exact (H.universalBranch_sameOneTypeBelow_iff w u v hwu hwv).mpr
      hsame a.val b.val hab hbw
  · have hbeq : b.val.last = w := by omega
    have hn := hwrong hbeq
    exact iff_of_false
      (H.no_branch_edge_wrong_middle a.val b.val w u hbeq hn)
      (H.no_branch_edge_wrong_middle a.val b.val w v hbeq hn)

/-- Auxiliary-type agreement includes all candidate tests at levels
at most w, except the cut vertex itself. -/
theorem relativeBranch_sameAuxType_at_boundary
    (H : Ordered3Graph Nat) {n : Nat}
    (I : EnumNode n) (hI : H.initialSegment n = I)
    (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w ≤ u₀) (hu : u₀ < u₁)
    (hwv : w ≤ v₀) (hv : v₀ < v₁)
    (hsame : H.SameAuxTypeBelow w u₀ u₁ v₀ v₁)
    (a : RelativeBranchNode I)
    (ha : a.val.last ≤ w)
    (hwrong : a.val.last = w → a.val ≠ H.branchNode w) :
    (relativeBranchGraph I).edge a
      (H.relativeBranchNode I hI u₀) (H.relativeBranchNode I hI u₁) ↔
    (relativeBranchGraph I).edge a
      (H.relativeBranchNode I hI v₀) (H.relativeBranchNode I hI v₁) := by
  change universalBranchGraph.edge a.val (H.branchNode u₀) (H.branchNode u₁) ↔
    universalBranchGraph.edge a.val (H.branchNode v₀) (H.branchNode v₁)
  by_cases haw : a.val.last < w
  · exact (H.universalBranch_sameAuxTypeBelow_iff
      w u₀ u₁ v₀ v₁ hwu hu hwv hv).mpr hsame a.val haw
  · have heq : a.val.last = w := by omega
    have hn := hwrong heq
    exact iff_of_false
      (H.no_branch_edge_wrong_first a.val w u₀ u₁ heq hn)
      (H.no_branch_edge_wrong_first a.val w v₀ v₁ heq hn)

end Ordered3Graph
end ThreeUniformDiaries
