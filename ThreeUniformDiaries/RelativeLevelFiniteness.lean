import ThreeUniformDiaries.RelativePrefixClosure

/-!
# Every level of the universal and relative branch hypergraphs is finite

The length-first enumeration of K_I requires more than countability:
it requires that each fixed enumeration length contribute only finitely
many nodes. The proof is explicit: a vertex with last index k is uniquely
determined by an EnumNode (k+1). Relative K_I inherits finiteness as a
subtype of the universal branch hypergraph.
-/

namespace ThreeUniformDiaries

/-- There are finitely many enumerated finite hypergraphs on each
fixed nonempty number of vertices. -/
theorem enumerationBranch_level_finite (k : Nat) :
    Set.Finite {A : EnumerationBranchNode | A.last = k} := by
  classical
  let f : EnumNode (k + 1) → EnumerationBranchNode :=
    fun E => ⟨k, E⟩
  apply (Set.finite_range f).subset
  intro A hA
  cases A with
  | mk last enumeration =>
    change last = k at hA
    subst last
    exact ⟨enumeration, rfl⟩

/-- Consequently K_I has finitely many vertices at any fixed last
index, regardless of the finite initial segment I. -/
theorem relativeBranch_level_finite
    {n : Nat} (I : EnumNode n) (k : Nat) :
    Set.Finite {A : RelativeBranchNode I | A.val.last = k} := by
  apply (enumerationBranch_level_finite k).preimage
  intro a _ b _ hab
  exact Subtype.val_injective hab

end ThreeUniformDiaries
