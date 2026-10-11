import ThreeUniformDiaries.RootGluedCoordinateCarrier

/-!
# Intrinsic order on the root-glued non-homogeneous three-type tree

The scalar tree has one new root and the three coordinate type trees
as its three incomparable root cones. Its order, immediate successors,
and levels are defined independently of any vector-subtree coding.

This is the actual scalar ambient tree needed to state the
non-homogeneous Milliken theorem, not an encoding that defines
scalar strong subtrees tautologically to be vector strong subtrees.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Root-glued three-coordinate type-tree node. -/
abbrev GluedNode := Option CoordNode

/-- Initial segment relation in the glued scalar tree. -/
def gluedLE : GluedNode → GluedNode → Prop
  | none, _ => True
  | some x, some y => x ≤ y
  | some _, none => False

/-- Immediate successors in the glued scalar tree. -/
def gluedChild : GluedNode → GluedNode → Prop
  | none, some y => level y = 0
  | some x, some y => x ⋖ y
  | _, _ => False

theorem gluedLE_refl (x : GluedNode) : gluedLE x x := by
  cases x with
  | none => trivial
  | some x => exact le_refl x

theorem gluedLE_trans {x y z : GluedNode}
    (hxy : gluedLE x y) (hyz : gluedLE y z) :
    gluedLE x z := by
  cases x with
  | none => trivial
  | some x =>
      cases y with
      | none => exact False.elim hxy
      | some y =>
          cases z with
          | none => exact False.elim hyz
          | some z => exact le_trans hxy hyz

theorem gluedLE_antisymm {x y : GluedNode}
    (hxy : gluedLE x y) (hyx : gluedLE y x) : x = y := by
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y => exact False.elim hyx
  | some x =>
      cases y with
      | none => exact False.elim hxy
      | some y => exact congrArg Option.some (le_antisymm hxy hyx)

/-- The new root is below every node, including itself. -/
theorem gluedLE_root (x : GluedNode) : gluedLE none x := by
  trivial

/-- No coordinate node lies below the added root. -/
theorem gluedLE_not_below_root (x : CoordNode) :
    ¬ gluedLE (some x) none := by
  intro h
  exact h

theorem gluedLE_some_iff (x y : CoordNode) :
    gluedLE (some x) (some y) ↔ x ≤ y := Iff.rfl

theorem gluedChild_root_iff (x : CoordNode) :
    gluedChild none (some x) ↔ level x = 0 := Iff.rfl

theorem gluedChild_some_iff (x y : CoordNode) :
    gluedChild (some x) (some y) ↔ x ⋖ y := Iff.rfl

/-- The glued root occupies scalar level zero. -/
theorem gluedLevel_none : gluedLevel none = 0 := rfl

/-- Each coordinate level is shifted by exactly one. -/
theorem gluedLevel_some (x : CoordNode) :
    gluedLevel (some x) = level x + 1 := rfl

theorem gluedLE_level_mono {x y : GluedNode}
    (hxy : gluedLE x y) :
    gluedLevel x ≤ gluedLevel y := by
  cases x with
  | none => exact Nat.zero_le _
  | some x =>
      cases y with
      | none => exact False.elim hxy
      | some y =>
          change level x + 1 ≤ level y + 1
          exact Nat.add_le_add_right (level_le_of_le hxy) 1

/-- All glued ambient root children have scalar level one. -/
theorem gluedChild_root_level {x : GluedNode}
    (h : gluedChild none x) : gluedLevel x = 1 := by
  cases x with
  | none => exact False.elim h
  | some x =>
      change level x = 0 at h
      simpa only [gluedLevel, h] using (rfl : (0 : Nat) + 1 = 1)

theorem gluedChild_level_succ {x y : GluedNode}
    (h : gluedChild x y) :
    gluedLevel y = gluedLevel x + 1 := by
  cases x with
  | none =>
      exact gluedChild_root_level h
  | some x =>
      cases y with
      | none => exact False.elim h
      | some y =>
          have hlev := covBy_level h
          change level y + 1 = (level x + 1) + 1
          omega

end CoordNode
end ThreeUniformDiaries
