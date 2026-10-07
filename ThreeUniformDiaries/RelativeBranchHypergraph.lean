import ThreeUniformDiaries.BranchHypergraph

/-!
# The relative universal branch hypergraph K_I

For a fixed finite initial segment I, the vertices of K_I are exactly
the nonempty finite hypergraphs which either are proper nonempty initial
segments of I or extend I.  These are a subtype of K_empty.

If H has initial segment I, the branch nodes H|_(v+1) lie in this
subtype, and all increasing triples are preserved and reflected.

This formalizes the basic `g_H : H → K_I` representation.  The separate
generic embedding `φ : K_I → G` and preservation of meet levels remain
to be established.
-/

namespace ThreeUniformDiaries

/-- Membership in the relative branch hypergraph K_I. -/
def InRelativeBranchGraph {n : Nat} (I : EnumNode n)
    (A : EnumerationBranchNode) : Prop :=
  (A.last + 1 < n →
    A.enumeration = I.truncate (A.last + 1)) ∧
  (n ≤ A.last + 1 →
    A.enumeration.truncate n = I)

/-- The vertex type of K_I. -/
abbrev RelativeBranchNode {n : Nat} (I : EnumNode n) :=
  {A : EnumerationBranchNode // InRelativeBranchGraph I A}

/-- K_I is the induced subgraph of K_empty on the selected vertices. -/
def relativeBranchGraph {n : Nat} (I : EnumNode n) :
    Ordered3Graph (RelativeBranchNode I) where
  edge a b c := universalBranchGraph.edge a.val b.val c.val

namespace Ordered3Graph

/-- Every H-initial segment has the relative I-compatibility property. -/
theorem branchNode_mem_relative
    (H : Ordered3Graph Nat) {n : Nat} (I : EnumNode n)
    (hI : H.initialSegment n = I) (v : Nat) :
    InRelativeBranchGraph I (H.branchNode v) := by
  constructor
  · intro hsmall
    have hle : v + 1 ≤ n := Nat.le_of_lt hsmall
    have h := H.initialSegment_truncate hle
    change H.initialSegment (v + 1) = I.truncate (v + 1)
    rw [← hI]
    exact h.symm
  · intro hlarge
    have h := H.initialSegment_truncate hlarge
    change (H.initialSegment (v + 1)).truncate n = I
    exact h.trans hI

/-- The relative branch map g_H. -/
noncomputable def relativeBranchNode
    (H : Ordered3Graph Nat) {n : Nat} (I : EnumNode n)
    (hI : H.initialSegment n = I) (v : Nat) :
    RelativeBranchNode I :=
  ⟨H.branchNode v, H.branchNode_mem_relative I hI v⟩

/-- The relative branch map is injective. -/
theorem relativeBranchNode_injective
    (H : Ordered3Graph Nat) {n : Nat} (I : EnumNode n)
    (hI : H.initialSegment n = I) :
    Function.Injective (H.relativeBranchNode I hI) := by
  intro i j h
  exact H.branchNode_injective (congrArg Subtype.val h)

/-- The relative g_H map preserves and reflects all increasing triples. -/
theorem relativeBranchNode_edge_iff
    (H : Ordered3Graph Nat) {n : Nat} (I : EnumNode n)
    (hI : H.initialSegment n = I)
    {i j k : Nat} (hij : i < j) (hjk : j < k) :
    (relativeBranchGraph I).edge
      (H.relativeBranchNode I hI i)
      (H.relativeBranchNode I hI j)
      (H.relativeBranchNode I hI k) ↔
    H.edge i j k := by
  change universalBranchGraph.edge
      (H.branchNode i) (H.branchNode j) (H.branchNode k) ↔ H.edge i j k
  exact H.branchNode_edge_iff hij hjk

end Ordered3Graph
end ThreeUniformDiaries
