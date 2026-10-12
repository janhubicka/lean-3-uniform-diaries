import ThreeUniformDiaries.RootGluedAmbientTree
import Milliken.GeneralTree

/-!
# Actual root-glued ambient rank is the shifted ATR type-tree rank

Milliken uses its own ambient rank, defined via iterated predecessor
in Mathlib RootedTree. The type-tree construction instead uses the
explicit length of the enumeration, 1-type or aux-type record.
This file verifies, on the *actual* root-glued ambient tree, that the
ranks agree. It is a necessary non-tautological bridge before the
three genuinely synchronized strong pictures can be inserted into
Milliken.GeneralTree.StrongSubtree.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Rank of a coordinate type-node in the actual `Milliken.AmbientTree`
is the coordinate rank plus the newly adjoined scalar root. -/
theorem rootGluedAmbient_level_coe (x : CoordNode) :
    rootGluedAmbientTree.level (x : WithBot CoordNode) =
      level x + 1 := by
  let U := rootGluedAmbientTree
  have hmain : ∀ n : ℕ, ∀ y : CoordNode,
      level y = n → U.level (y : WithBot CoordNode) = n + 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro y hy
      by_cases hn : n = 0
      · subst n
        have hrootchild : gluedChild (⊥ : WithBot CoordNode) (y : WithBot CoordNode) := by
          change level y = 0
          exact hy
        have hcov :
            (⊥ : WithBot CoordNode) ⋖ (y : WithBot CoordNode) :=
          (gluedChild_iff_covBy _ _).mp hrootchild
        have hlevel := U.level_covBy hcov
        have hroot : U.level (⊥ : WithBot CoordNode) = 0 :=
          U.level_root
        rw [hroot] at hlevel
        simpa only [Nat.zero_add] using hlevel
      · have hnpos : 0 < n := by omega
        let p := truncate y (n - 1)
        have hpLevel : level p = n - 1 := by simp [p]
        have hpLe : p ≤ y := by
          apply truncate_le y
          rw [hy]
          omega
        have hpChild : p ⋖ y := by
          apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpLe
          rw [hpLevel, hy]
          omega
        have hcov :
            (p : WithBot CoordNode) ⋖ (y : WithBot CoordNode) :=
          (gluedChild_iff_covBy _ _).mp hpChild
        have hprev : U.level (p : WithBot CoordNode) = (n - 1) + 1 :=
          ih (n - 1) (by omega) p hpLevel
        have hnext := U.level_covBy hcov
        rw [hprev] at hnext
        omega
  exact hmain (level x) x rfl

/-- Exact rank compatibility, including the new root. -/
theorem rootGluedAmbient_level_eq_gluedLevel
    (x : WithBot CoordNode) :
    rootGluedAmbientTree.level x = gluedLevel x := by
  cases x with
  | bot =>
      exact rootGluedAmbientTree.level_root
  | coe y =>
      exact rootGluedAmbient_level_coe y

end CoordNode
end ThreeUniformDiaries
