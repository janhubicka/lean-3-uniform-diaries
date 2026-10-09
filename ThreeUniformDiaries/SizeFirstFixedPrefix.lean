import ThreeUniformDiaries.SizeFirstSourceTests

/-!
# The fixed initial segment of a size-first relative K_I presentation

For an original H extending I, the canonical branch indices of its
first |I| vertices are literally the first |I| source indices. This
is required when the inherited target construction fixes a prescribed
nonempty prefix; length monotonicity alone would only give an
order-preserving reindexing.
-/

namespace ThreeUniformDiaries
namespace SizeFirstBranchPresentation

variable {n : Nat} {I : EnumNode n} (E : SizeFirstBranchPresentation I)

/-- No reindexing occurs on the original I-prefix of a canonical branch. -/
theorem branchIndex_fixed_prefix
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (k : Nat) (hk : k < n) :
    E.branchIndex H hI k = k := by
  apply E.code.injective
  rw [E.code_branchIndex H hI k, E.initial_source_nodes k hk]
  apply Subtype.ext
  change H.branchNode k = (relativeBranchCanonical I k).val
  have hprefix : H.initialSegment (k + 1) = I.truncate (k + 1) := by
    rw [← hI]
    exact (H.initialSegment_truncate (by omega)).symm
  exact congrArg (fun A : EnumNode (k + 1) =>
    (⟨k, A⟩ : EnumerationBranchNode)) hprefix

/-- Every edge entirely inside the fixed prefix is already correctly
represented by the source graph's length-first enumeration. -/
theorem graph_prefix_edge_iff
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    {a b c : Nat} (hab : a < b) (hbc : b < c) (hc : c < n) :
    E.graph.edge a b c ↔ H.edge a b c := by
  have h := E.graph_branch_edge_iff H hI hab hbc
  have ha : a < n := by omega
  have hb : b < n := by omega
  simpa only [
    E.branchIndex_fixed_prefix H hI a ha,
    E.branchIndex_fixed_prefix H hI b hb,
    E.branchIndex_fixed_prefix H hI c hc
  ] using h

end SizeFirstBranchPresentation
end ThreeUniformDiaries
