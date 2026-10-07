import ThreeUniformDiaries.RelativeBranchHypergraph

/-!
# Countability of the universal enumeration hypergraphs

The proof of Lemma `lem:Kiemb` enumerates all vertices of K_I in an order
extending the initial-segment order.  This file verifies the countability
prerequisite: every finite enumeration level is finite, and the union over
all finite levels is countable.

Constructing the specific topological ordering and generic embedding is
a separate task.
-/

namespace ThreeUniformDiaries

noncomputable instance enumerationBranchNodeCountable :
    Countable EnumerationBranchNode := by
  classical
  let f : EnumerationBranchNode → (Σ n : Nat, EnumNode (n + 1)) :=
    fun x => ⟨x.last, x.enumeration⟩
  have hinj : Function.Injective f := by
    intro x y h
    cases x
    cases y
    cases h
    rfl
  exact Countable.of_injective f hinj

/-- In particular the relative class of branch nodes K_I is countable. -/
noncomputable instance relativeBranchNodeCountable
    {n : Nat} (I : EnumNode n) :
    Countable (RelativeBranchNode I) := inferInstance

end ThreeUniformDiaries
