import ThreeUniformDiaries.RootGluedZeroFibres

/-!
# Intrinsic scalar strong subtrees of the root-glued three-type tree

Milliken's theorem must be applied to the actual rooted scalar
tree, not to a datatype of synchronized vector subtrees declared
by fiat. We therefore define the scalar strong-subtree conditions
directly in terms of the glued tree's order, immediate child
relation and ambient meet.

There is a single root at scalar level 0, followed by the common
selected coordinate levels f(i)+1. The root's three successor
cones and all successor cones above them must have exactly one
retained representative at the next selected height.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The ambient rooted-tree meet after gluing the three disconnected
type-tree components below one additional root. -/
noncomputable def gluedMeet : GluedNode → GluedNode → GluedNode
  | none, _ => none
  | _, none => none
  | some x, some y =>
      if sort x = sort y then some (CoordNode.meet x y) else none

@[simp] theorem gluedMeet_none_left (x : GluedNode) :
    gluedMeet none x = none := by
  cases x <;> rfl

@[simp] theorem gluedMeet_none_right (x : GluedNode) :
    gluedMeet x none = none := by
  cases x <;> rfl

theorem gluedMeet_some_same
    (x y : CoordNode) (h : sort x = sort y) :
    gluedMeet (some x) (some y) = some (CoordNode.meet x y) := by
  simp [gluedMeet, h]

theorem gluedMeet_some_different
    (x y : CoordNode) (h : sort x ≠ sort y) :
    gluedMeet (some x) (some y) = none := by
  simp [gluedMeet, h]

/-- A synchronized selected level map in the scalar glued tree:
the added root is level 0, and coordinate level f(i) shifts to f(i)+1. -/
def gluedSelectedLevel (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => f i + 1

@[simp] theorem gluedSelectedLevel_zero (f : Nat → Nat) :
    gluedSelectedLevel f 0 = 0 := rfl

@[simp] theorem gluedSelectedLevel_succ (f : Nat → Nat) (i : Nat) :
    gluedSelectedLevel f (i + 1) = f i + 1 := rfl

theorem gluedSelectedLevel_strictMono (f : Nat → Nat) (hf : StrictMono f) :
    StrictMono (gluedSelectedLevel f) := by
  apply strictMono_nat_of_lt_succ
  intro i
  cases i with
  | zero =>
      change 0 < f 0 + 1
      omega
  | succ i =>
      change f i + 1 < f (i + 1) + 1
      exact Nat.add_lt_add_right (hf (Nat.lt_succ_self i)) 1

/-- Intrinsic non-homogeneous scalar infinite strong subtree of the
glued ambient tree, with exactly one representative per ambient cone.
The coordinate levels may have arbitrarily large, unbounded fanout. -/
structure RootedGluedInfiniteStrong
    (W : Set GluedNode) (f : Nat → Nat) : Prop where
  root_mem : none ∈ W
  meet_closed : ∀ x ∈ W, ∀ y ∈ W, gluedMeet x y ∈ W
  selected_levels : ∀ x ∈ W,
    x = none ∨ ∃ i : Nat, gluedLevel x = f i + 1
  all_levels : ∀ i : Nat, ∃ x ∈ W, gluedLevel x = f i + 1
  root_child : ∀ t : GluedNode, gluedChild none t →
    ∃! z : GluedNode,
      z ∈ W ∧ gluedLevel z = f 0 + 1 ∧ gluedLE t z
  next_child : ∀ (i : Nat) (p : GluedNode),
    p ∈ W → gluedLevel p = f i + 1 →
    ∀ t : GluedNode, gluedChild p t →
    ∃! z : GluedNode,
      z ∈ W ∧ gluedLevel z = f (i + 1) + 1 ∧ gluedLE t z

/-- Intrinsic scalar strongness has the global root automatically. -/
theorem rootedGluedInfiniteStrong_root
    {W : Set GluedNode} {f : Nat → Nat}
    (hW : RootedGluedInfiniteStrong W f) :
    none ∈ W := hW.root_mem

end CoordNode
end ThreeUniformDiaries
