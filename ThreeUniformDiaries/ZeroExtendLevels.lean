import ThreeUniformDiaries.PrunedTypeTrees

/-!
# Extending type-tree nodes to an arbitrary later level

The finite strong-subtree completion needs to fill missing successor
directions. The type-tree coordinates are pruned: each node has a
canonical all-zero immediate successor. Iterate that operation to
reach any larger selected level, without changing the original prefix.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The one-step zero extension preserves the original node as
an ancestor. -/
theorem le_zeroChild (x : CoordNode) : x ≤ zeroChild x := by
  refine ⟨by simp, ?_⟩
  exact truncate_zeroChild x

/-- Add d successive all-zero levels to a coordinate-tree node. -/
def zeroExtend (x : CoordNode) : Nat → CoordNode
  | 0 => x
  | d + 1 => zeroChild (zeroExtend x d)

/-- Iterated zero extension increases the level by exactly d. -/
@[simp] theorem level_zeroExtend (x : CoordNode) (d : Nat) :
    level (zeroExtend x d) = level x + d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [zeroExtend, ih, Nat.add_succ]

/-- The original node is an ancestor of every zero extension. -/
theorem le_zeroExtend (x : CoordNode) (d : Nat) :
    x ≤ zeroExtend x d := by
  induction d with
  | zero =>
      exact le_refl x
  | succ d ih =>
      exact le_trans ih (le_zeroChild (zeroExtend x d))

/-- A concrete extension to any prescribed level at least the current
one, obtained by adding exactly the missing number of zero levels. -/
def zeroExtendTo (x : CoordNode) (L : Nat) (h : level x ≤ L) :
    CoordNode :=
  zeroExtend x (L - level x)

/-- The chosen extension lies at the requested level exactly. -/
@[simp] theorem level_zeroExtendTo
    (x : CoordNode) (L : Nat) (h : level x ≤ L) :
    level (zeroExtendTo x L h) = L := by
  simp [zeroExtendTo]
  omega

/-- The chosen extension preserves all bits of the input prefix. -/
theorem le_zeroExtendTo
    (x : CoordNode) (L : Nat) (h : level x ≤ L) :
    x ≤ zeroExtendTo x L h := by
  exact le_zeroExtend x (L - level x)

end CoordNode
end ThreeUniformDiaries
