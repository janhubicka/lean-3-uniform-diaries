import ThreeUniformDiaries.RootGluedTreeOrder
import ThreeUniformDiaries.PrunedTypeTrees

/-!
# The root-glued three-type scalar tree is finite-branching and pruned

The direct non-homogeneous version of Milliken (Milliken 1979) applies
to finitely branching rooted trees with no terminal nodes. These
ambient hypotheses are proved explicitly for the scalar tree that
is obtained by adjoining one root below E0, E1, E2.

No uniform bound on branching is assumed: the number of immediate
successors grows with the type-tree level.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem gluedChild_finite (p : GluedNode) :
    Set.Finite {q : GluedNode | gluedChild p q} := by
  cases p with
  | none =>
      have hfin :=
        (level_finite 0).image (fun x => (some x : GluedNode))
      apply hfin.subset
      intro q hq
      cases q with
      | none =>
          exact False.elim hq
      | some x =>
          change level x = 0 at hq
          exact ⟨x, hq, rfl⟩
  | some p =>
      have hfin :=
        (level_finite (level p + 1)).image
          (fun x => (some x : GluedNode))
      apply hfin.subset
      intro q hq
      cases q with
      | none =>
          exact False.elim hq
      | some x =>
          have hx : level x = level p + 1 :=
            covBy_level hq
          exact ⟨x, hx, rfl⟩

theorem gluedChild_exists (p : GluedNode) :
    ∃ q : GluedNode, gluedChild p q := by
  cases p with
  | none =>
      refine ⟨some (.aux 0 (AuxNode.zero 0)), ?_⟩
      rfl
  | some p =>
      refine ⟨some (zeroChild p), ?_⟩
      have hp : p ≤ zeroChild p :=
        ⟨by simp, truncate_zeroChild p⟩
      apply SuccessorTree.LevelTree.covBy_of_le_level_succ hp
      exact level_zeroChild p

/-- The newly added scalar root has finitely many immediate children
and every scalar node, including the root, has a child. -/
theorem glued_ambient_milliken_hypotheses :
    (∀ p : GluedNode, Set.Finite {q : GluedNode | gluedChild p q}) ∧
    (∀ p : GluedNode, ∃ q, gluedChild p q) := by
  exact ⟨gluedChild_finite, gluedChild_exists⟩

end CoordNode
end ThreeUniformDiaries
