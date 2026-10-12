import ThreeUniformDiaries.RootGluedMeetSemilattice
import ThreeUniformDiaries.TypeForestPredOrder
import ThreeUniformDiaries.RootGluedFinitePruned
import Milliken.AmbientTree

/-!
# The genuine arbitrary-branching ATR ambient tree

Attach one root beneath the actual E0, E1 and E2 type forests.
The global greatest-common-predecessor semilattice comes from
`RootGluedMeetSemilattice`; the predecessor order is inherited from
deleting one genuine type-tree coordinate and from the new root.

No globally fixed branching alphabet or degree bound occurs.
We use Mathlib's actual `RootedTree` and Milliken's actual
`AmbientTree`, not a synthetic vector strong-subtree interface.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The old component roots are exactly the minimal nodes in the
coordinate forest. -/
theorem isMin_iff_level_zero (x : CoordNode) :
    IsMin x ↔ level x = 0 := by
  constructor
  · intro hmin
    have hle : x ≤ truncate x 0 :=
      hmin (truncate x 0) (truncate_le x (Nat.zero_le _))
    have hh := level_le_of_le hle
    simp only [level_truncate] at hh
    omega
  · intro hx
    intro y hy
    have hle : level y ≤ level x := level_le_of_le hy
    have hlevel : level y = level x := by omega
    exact (eq_of_le_of_level_eq hy hlevel).symm.le

/-- The concrete scalar child relation is literally order covering
in Mathlib's bottom-extended forest, including all three root cones. -/
theorem gluedChild_iff_covBy
    (a b : WithBot CoordNode) :
    gluedChild a b ↔ a ⋖ b := by
  cases a with
  | bot =>
      cases b with
      | bot =>
          simp [gluedChild, WithBot.not_covBy_bot]
      | coe y =>
          change level y = 0 ↔
            (⊥ : WithBot CoordNode) ⋖ (y : WithBot CoordNode)
          exact (isMin_iff_level_zero y).symm.trans
            (WithBot.bot_covBy_coe (a := y)).symm
  | coe x =>
      cases b with
      | bot =>
          simp [gluedChild, WithBot.not_covBy_bot]
      | coe y =>
          change x ⋖ y ↔
            ((x : WithBot CoordNode) ⋖ (y : WithBot CoordNode))
          exact (WithBot.coe_covBy_coe (a := y) (b := x)).symm

/-- Mathlib's rooted tree of the actual scalar three-type carrier.
The well-founded strict ancestry supplies predecessor-archimedeanness,
also at the level-zero-to-added-root step. -/
noncomputable def rootGluedRootedTree : RootedTree := by
  classical
  exact {
    α := WithBot CoordNode
    semilatticeInf := inferInstance
    orderBot := inferInstance
    predOrder := inferInstance
    isPredArchimedean := inferInstance
  }

/-- The exact locally finite, pruned, unbounded-degree ambient tree
on which the heterogeneous Milliken theorem must be applied. -/
noncomputable def rootGluedAmbientTree : Milliken.AmbientTree where
  toRootedTree := rootGluedRootedTree
  finite_children := by
    intro x
    change ({q : WithBot CoordNode | x ⋖ q} :
      Set (WithBot CoordNode)).Finite
    have heq :
        {q : WithBot CoordNode | x ⋖ q} =
          {q : WithBot CoordNode | gluedChild x q} := by
      ext q
      exact (gluedChild_iff_covBy x q).symm
    rw [heq]
    exact gluedChild_finite x
  has_child := by
    intro x
    obtain ⟨y, hy⟩ := gluedChild_exists x
    exact ⟨y, (gluedChild_iff_covBy x y).mp hy⟩

end CoordNode
end ThreeUniformDiaries
