import ThreeUniformDiaries.CoordinateTree

/-!
# No terminal nodes in the type-tree forest

Each node of the enumeration, 1-type, or auxiliary-type tree can be
extended by adding an all-zero new level.  This verifies the pruning
hypothesis needed when passing to infinite strong subtrees.
-/

namespace ThreeUniformDiaries

namespace AuxNode

def zero (n : Nat) : AuxNode n where
  bit := fun _ => false
  support := by intro i hi; rfl

end AuxNode

namespace OneNode

def zero (n : Nat) : OneNode n where
  pair := fun _ _ => false
  support := by intro i j h; rfl

end OneNode

namespace CoordNode

/-- A canonical immediate extension of any node, chosen with zero new data. -/
def zeroChild : CoordNode → CoordNode
  | .aux n a => .aux (n + 1) (a.succ false)
  | .one n a => .one (n + 1) (a.succ (AuxNode.zero n))
  | .enum n a => .enum (n + 1) (a.succ (OneNode.zero n))

@[simp] theorem level_zeroChild (x : CoordNode) :
    level (zeroChild x) = level x + 1 := by
  cases x <;> rfl

@[simp] theorem truncate_zeroChild (x : CoordNode) :
    truncate (zeroChild x) (level x) = x := by
  cases x with
  | aux n a => simp [zeroChild, truncate, level]
  | one n a => simp [zeroChild, truncate, level]
  | enum n a => simp [zeroChild, truncate, level]

/-- Every type-tree node has an immediate successor. -/
instance : SuccessorTree.PrunedTree CoordNode where
  exists_covBy := by
    intro x
    refine ⟨zeroChild x, ?_⟩
    have hx : x ≤ zeroChild x := by
      exact ⟨by simp, truncate_zeroChild x⟩
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hx
    exact level_zeroChild x

end CoordNode
end ThreeUniformDiaries
