import ThreeUniformDiaries.FixedPrefixCountableEmbedding

/-!
# Repaired C2 at every step of the fixed-prefix countable embedding

The one-root inherited recursion has an explicit global C2 theorem.
The genuine K_I application also needs the version whose first n0
source vertices are fixed and no choices are made before that prefix.

At stage t the new source vertex is n0+t; its designated parent has
an index below n0+t.  This module extracts the exact inherited
and zero clauses for the *eventual infinite embedding*, not merely
its finite approximation.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

variable (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
variable (n0 : Nat) (hI : K.initialSegment n0 = G.graph.initialSegment n0)
variable (parent : PrefixParentSchedule n0)

/-- The eventual image of the new vertex n0+t is precisely the
chosen successor witness of the stage containing its predecessors. -/
theorem fixedInherited_newImage (t : Nat) :
    G.fixedInheritedEmbedding K n0 hI parent (n0 + t) =
      (G.fixedInheritedStages K n0 hI parent t).inheritedVertex
        (parent t) := by
  let S := G.fixedInheritedStages K n0 hI parent t
  have hstage :
      (S.extendInherited (parent t)).image (Fin.last (n0 + t)) =
        ⟨S.inheritedVertex (parent t), by
          have hh := (S.inheritedVertex_spec (parent t)).1
          omega⟩ := by
    apply Fin.ext
    exact FiniteGenericStage.extendInherited_last S (parent t)
  have hfuture :=
    G.fixedInheritedEmbedding_at_stage K n0 hI parent (t + 1)
      (n0 + t) (by omega)
  have hval : ((S.extendInherited (parent t)).image
      (Fin.last (n0 + t))).val =
        G.fixedInheritedEmbedding K n0 hI parent (n0 + t) := by
    simpa [S, fixedInheritedStages, Nat.add_assoc] using hfuture
  exact hval.symm.trans (congrArg Fin.val hstage)

/-- A target vertex outside the complete image of a fixed-prefix
embedding is absent from every finite source stage. -/
theorem fixedInherited_omitted_stage (t x : Nat)
    (hmiss : ∀ i : Nat, G.fixedInheritedEmbedding K n0 hI parent i ≠ x) :
    ¬ ∃ j : Fin (n0 + t),
      ((G.fixedInheritedStages K n0 hI parent t).image j).val = x := by
  rintro ⟨j, hj⟩
  have hstable := G.fixedInheritedEmbedding_at_stage K n0 hI parent
    t j.val j.isLt
  exact hmiss j.val (hstable.symm.trans hj)

/-- Exact repaired C2 for target pairs with an omitted endpoint
at a fixed-prefix construction step. -/
theorem fixedInherited_gap_step (t : Nat)
    (x y : Fin ((G.fixedInheritedStages K n0 hI parent t).bound))
    (hxy : x < y)
    (hgap :
      (¬ ∃ i : Fin (n0 + t),
         (G.fixedInheritedStages K n0 hI parent t).image i = x) ∨
      (¬ ∃ j : Fin (n0 + t),
         (G.fixedInheritedStages K n0 hI parent t).image j = y)) :
    (y < (G.fixedInheritedStages K n0 hI parent t).image (parent t) →
      (G.graph.edge x.val y.val
        (G.fixedInheritedEmbedding K n0 hI parent (n0 + t)) ↔
       G.graph.edge x.val y.val
        (G.fixedInheritedEmbedding K n0 hI parent (parent t).val))) ∧
    ((G.fixedInheritedStages K n0 hI parent t).image (parent t) ≤ y →
      ¬ G.graph.edge x.val y.val
        (G.fixedInheritedEmbedding K n0 hI parent (n0 + t))) := by
  let S := G.fixedInheritedStages K n0 hI parent t
  have hnew := G.fixedInherited_newImage K n0 hI parent t
  have hpar : (S.image (parent t)).val =
      G.fixedInheritedEmbedding K n0 hI parent (parent t).val :=
    G.fixedInheritedEmbedding_at_stage K n0 hI parent
      t (parent t).val (parent t).isLt
  constructor
  · intro hy
    have h := (S.inheritedVertex_spec (parent t)).2.2.1
      x y hxy hgap hy
    rw [hnew, ← hpar]
    exact h
  · intro hy
    have h := (S.inheritedVertex_spec (parent t)).2.2.2
      x y hxy hgap hy
    rw [hnew]
    exact h

end GenericEnumerated3Graph
end ThreeUniformDiaries
