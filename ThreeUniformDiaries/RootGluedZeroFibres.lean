import ThreeUniformDiaries.RootGluedTreeOrder
import ThreeUniformDiaries.InfiniteCanonicalAux

/-!
# The unique zero-level node in each of the three type-tree coordinates

In the root-glued scalar tree, the added root has precisely three
ambient immediate successor cones, the unique E0, E1 and E2
coordinate nodes at level zero.

These elementary fibre-uniqueness lemmas make it possible to prove
that a glued strong vector picture has exactly one selected
representative in each root cone, using its three coordinate roots.
-/

namespace ThreeUniformDiaries

namespace AuxNode
theorem unique_zero (a b : AuxNode 0) : a = b := by
  apply AuxNode.ext_bits
  funext i
  exact (a.support i (Nat.zero_le i)).trans
    (b.support i (Nat.zero_le i)).symm
end AuxNode

namespace OneNode
theorem unique_zero (a b : OneNode 0) : a = b := by
  apply OneNode.ext_pairs
  funext i j
  have hbad : ¬ (i < j ∧ j < 0) := by
    intro h
    exact Nat.not_lt_zero j h.2
  exact (a.support i j hbad).trans (b.support i j hbad).symm
end OneNode

namespace EnumNode
theorem unique_zero (a b : EnumNode 0) : a = b := by
  apply EnumNode.ext_triples
  funext i j k
  have hbad : ¬ (i < j ∧ j < k ∧ k < 0) := by
    intro h
    exact Nat.not_lt_zero k h.2.2
  exact (a.support i j k hbad).trans
    (b.support i j k hbad).symm
end EnumNode

namespace CoordNode

/-- A zero-level auxiliary type lies below every auxiliary type. -/
theorem aux_zero_le (a : AuxNode 0) {n : Nat} (b : AuxNode n) :
    CoordNode.aux 0 a ≤ CoordNode.aux n b := by
  refine ⟨Nat.zero_le n, ?_⟩
  change CoordNode.aux 0 (b.truncate 0) = CoordNode.aux 0 a
  exact congrArg (CoordNode.aux 0)
    (AuxNode.unique_zero (b.truncate 0) a)

/-- A zero-level singleton type lies below every singleton type. -/
theorem one_zero_le (a : OneNode 0) {n : Nat} (b : OneNode n) :
    CoordNode.one 0 a ≤ CoordNode.one n b := by
  refine ⟨Nat.zero_le n, ?_⟩
  change CoordNode.one 0 (b.truncate 0) = CoordNode.one 0 a
  exact congrArg (CoordNode.one 0)
    (OneNode.unique_zero (b.truncate 0) a)

/-- A zero-level enumeration lies below every enumeration type. -/
theorem enum_zero_le (a : EnumNode 0) {n : Nat} (b : EnumNode n) :
    CoordNode.enum 0 a ≤ CoordNode.enum n b := by
  refine ⟨Nat.zero_le n, ?_⟩
  change CoordNode.enum 0 (b.truncate 0) = CoordNode.enum 0 a
  exact congrArg (CoordNode.enum 0)
    (EnumNode.unique_zero (b.truncate 0) a)

/-- Any retained node at the first selected level of a strong
coordinate picture equals its chosen root. -/
theorem strong_root_unique_at_first_level
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (hr : level r = f 0)
    (x : CoordNode) (hx : x ∈ S)
    (hxLevel : level x = f 0) :
    x = r := by
  exact (eq_of_le_of_level_eq
    (hS.root_le x hx) (hr.trans hxLevel.symm)).symm

end CoordNode
end ThreeUniformDiaries
