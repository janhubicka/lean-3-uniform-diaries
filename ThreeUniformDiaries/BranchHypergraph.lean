import ThreeUniformDiaries.InfinitePrefixes

/-!
# The universal branch hypergraph

For the empty initial segment, the manuscript's K_I has one vertex for
each nonempty enumerated finite hypergraph. Such a vertex can be represented
by its last index and its finite enumeration node.

Three vertices form a hyperedge exactly when the enumeration nodes form a
chain and their three last indices form an edge in the largest hypergraph.

The branch map `g_H(v)=H|_(v+1)` is injective and preserves and reflects
all increasing triples, as required by the manuscript.
-/

namespace ThreeUniformDiaries

/-- A vertex of the universal enumeration hypergraph `K_∅`. -/
structure EnumerationBranchNode where
  last : Nat
  enumeration : EnumNode (last + 1)

/-- The hypergraph on nonempty finite enumerated hypergraphs, with edges
restricted to strictly increasing chains as in the manuscript. -/
def universalBranchGraph : Ordered3Graph EnumerationBranchNode where
  edge a b c :=
    a.last < b.last ∧ b.last < c.last ∧
    b.enumeration.truncate (a.last + 1) = a.enumeration ∧
    c.enumeration.truncate (b.last + 1) = b.enumeration ∧
    c.enumeration.triple a.last b.last c.last = true

namespace Ordered3Graph

/-- The vertex `H|_(v+1)` of the universal branch hypergraph. -/
noncomputable def branchNode (H : Ordered3Graph Nat) (v : Nat) :
    EnumerationBranchNode :=
  ⟨v, H.initialSegment (v + 1)⟩

@[simp] theorem branchNode_last (H : Ordered3Graph Nat) (v : Nat) :
    (H.branchNode v).last = v := rfl

theorem branchNode_injective (H : Ordered3Graph Nat) :
    Function.Injective H.branchNode := by
  intro i j h
  exact congrArg EnumerationBranchNode.last h

/-- Along a branch, later finite enumerations restrict to earlier ones. -/
theorem branchNode_chain (H : Ordered3Graph Nat)
    {i j : Nat} (hij : i ≤ j) :
    (H.branchNode j).enumeration.truncate (i + 1) =
      (H.branchNode i).enumeration := by
  exact H.initialSegment_truncate (Nat.succ_le_succ hij)

/-- Exactly the original increasing triples become edges of branch nodes. -/
theorem branchNode_edge_iff (H : Ordered3Graph Nat)
    {i j k : Nat} (hij : i < j) (hjk : j < k) :
    universalBranchGraph.edge (H.branchNode i) (H.branchNode j) (H.branchNode k) ↔
      H.edge i j k := by
  change
    (i < j ∧ j < k ∧
      (H.initialSegment (j + 1)).truncate (i + 1) =
        H.initialSegment (i + 1) ∧
      (H.initialSegment (k + 1)).truncate (j + 1) =
        H.initialSegment (j + 1) ∧
      (H.initialSegment (k + 1)).triple i j k = true) ↔ H.edge i j k
  have hpre_i :
      (H.initialSegment (j + 1)).truncate (i + 1) =
        H.initialSegment (i + 1) :=
    H.initialSegment_truncate (Nat.succ_le_succ hij.le)
  have hpre_j :
      (H.initialSegment (k + 1)).truncate (j + 1) =
        H.initialSegment (j + 1) :=
    H.initialSegment_truncate (Nat.succ_le_succ hjk.le)
  have hedge := H.initialSegment_edge_iff hij hjk (Nat.lt_succ_self k)
  constructor
  · intro h
    exact hedge.mp h.2.2.2.2
  · intro h
    exact ⟨hij, hjk, hpre_i, hpre_j, hedge.mpr h⟩

end Ordered3Graph
end ThreeUniformDiaries
