import ThreeUniformDiaries.TypeTrees
import ThreeUniformDiaries.AuxTypes

/-!
# Finite prefixes of infinite enumerated hypergraphs

An infinite enumerated 3-uniform hypergraph determines the sequence of
finite enumeration nodes appearing in the manuscript's `g_H` construction.
We verify that the initialSegment nodes are nested and that they retain exactly the
edges on increasing triples inside the finite initial segment.

The branch-hypergraph map `g_H(v) = H|_(v+1)` will be built on top of
these initialSegment nodes.
-/

namespace ThreeUniformDiaries

namespace Ordered3Graph

/-- The finite enumerated hypergraph induced by the first `n` vertices
of a hypergraph on the natural numbers. Non-increasing triples are zero. -/
noncomputable def initialSegment (H : Ordered3Graph Nat) (n : Nat) : EnumNode n := by
  classical
  refine {
    triple := fun i j k =>
      decide (i < j ∧ j < k ∧ k < n ∧ H.edge i j k)
    support := ?_
  }
  intro i j k hbad
  have hnot : ¬ (i < j ∧ j < k ∧ k < n ∧ H.edge i j k) := by
    intro h
    exact hbad ⟨h.1, h.2.1, h.2.2.1⟩
  simp [hnot]

/-- A initialSegment remembers precisely the increasing triples of the ambient
hypergraph that lie below its cut. -/
theorem prefix_edge_iff (H : Ordered3Graph Nat)
    {n i j k : Nat} (hij : i < j) (hjk : j < k) (hkn : k < n) :
    (H.initialSegment n).triple i j k = true ↔ H.edge i j k := by
  classical
  simp [initialSegment, hij, hjk, hkn]

/-- Restricting a longer initialSegment gives the shorter initialSegment. -/
theorem prefix_truncate (H : Ordered3Graph Nat)
    {n m : Nat} (hnm : n ≤ m) :
    (H.initialSegment m).truncate n = H.initialSegment n := by
  classical
  apply EnumNode.ext_triples
  funext i j k
  change
    (if k < n then
       decide (i < j ∧ j < k ∧ k < m ∧ H.edge i j k)
     else false) =
    decide (i < j ∧ j < k ∧ k < n ∧ H.edge i j k)
  by_cases hk : k < n
  · have hkm : k < m := lt_of_lt_of_le hk hnm
    simp [hk, hkm]
  · simp [hk]

/-- In particular consecutive prefixes are linked by restriction. -/
theorem prefix_succ_truncate (H : Ordered3Graph Nat) (n : Nat) :
    (H.initialSegment (n + 1)).truncate n = H.initialSegment n :=
  H.prefix_truncate (Nat.le_succ n)

end Ordered3Graph
end ThreeUniformDiaries
