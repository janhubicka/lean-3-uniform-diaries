import ThreeUniformDiaries.KIBranchTargetAgreement

/-!
# Every selected first vertex in a branch auxiliary edge is a branch prefix

The 3-uniform universal branch hypergraph only has edges along
initial-segment chains. Consequently if two vertices of a triple
are on a fixed canonical branch and its third (earlier) vertex is
selected from K_I, that earlier vertex must also belong to the
same canonical branch. This proves that selected K_I nodes outside
the branch do not contribute auxiliary tests.

This complements GlobalGapInheritance, which deals with vertices
not selected in the global K_I image at all.
-/

namespace ThreeUniformDiaries

/-- A selected node forming an auxiliary edge through two later
canonical branch nodes is necessarily itself the matching finite
initial segment of H. -/
theorem selected_aux_edge_implies_branch_prefix
    (H : Ordered3Graph Nat) {n : Nat}
    (I : EnumNode n) (hI : H.initialSegment n = I)
    (A : RelativeBranchNode I) (u v : Nat)
    (huv : u < v)
    (hedge : (relativeBranchGraph I).edge A
      (H.relativeBranchNode I hI u)
      (H.relativeBranchNode I hI v)) :
    A = H.relativeBranchNode I hI A.val.last := by
  have haux : universalBranchGraph.edge A.val
      (H.branchNode u) (H.branchNode v) := hedge
  have hau : A.val.last < u := haux.1
  have hsame :
      H.initialSegment (A.val.last + 1) = A.val.enumeration :=
    (H.universalBranch_edge_aux_prefix_iff A.val hau huv).mp haux |>.1 |>.symm
  apply Subtype.ext
  exact A.val.eq_branchNode_of_prefix H A.val.last rfl hsame.symm

/-- Any selected K_I node which is not on the canonical branch
cannot give an auxiliary hyperedge with two later branch vertices. -/
theorem selected_offbranch_aux_zero
    (H : Ordered3Graph Nat) {n : Nat}
    (I : EnumNode n) (hI : H.initialSegment n = I)
    (A : RelativeBranchNode I) (u v : Nat) (huv : u < v)
    (hmiss : A ≠ H.relativeBranchNode I hI A.val.last) :
    ¬ (relativeBranchGraph I).edge A
      (H.relativeBranchNode I hI u)
      (H.relativeBranchNode I hI v) := by
  intro he
  exact hmiss (selected_aux_edge_implies_branch_prefix H I hI A u v huv he)

namespace SizeFirstBranchPresentation

variable {n : Nat} {I : EnumNode n} (E : SizeFirstBranchPresentation I)

/-- An indexed selected K_I vertex contributing an auxiliary test
must be the canonical branch index at its own source length. -/
theorem indexed_aux_edge_implies_branch_index
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (a u v : Nat) (huv : u < v)
    (hedge : E.graph.edge a (E.branchIndex H hI u)
      (E.branchIndex H hI v)) :
    a = E.branchIndex H hI (E.code a).val.last := by
  have hsource : (relativeBranchGraph I).edge
      (E.code a) (H.relativeBranchNode I hI u)
      (H.relativeBranchNode I hI v) := by
    simpa [graph] using hedge
  have hprefix := selected_aux_edge_implies_branch_prefix
    H I hI (E.code a) u v huv hsource
  have hcode : E.code a =
      E.code (E.branchIndex H hI (E.code a).val.last) := by
    rw [E.code_branchIndex H hI]
    exact hprefix
  exact E.code.injective hcode

end SizeFirstBranchPresentation
end ThreeUniformDiaries
