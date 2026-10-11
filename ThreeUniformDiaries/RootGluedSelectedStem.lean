import ThreeUniformDiaries.RootGluedCarrierEquiv
import ThreeUniformDiaries.RootGluedTreeOrder

/-!
# Root-glued selected stems of the ATR three-coordinate type trees

Root-gluing shifts vector source level j to scalar source level j+1.
This file packages the shift and the exact finite approximation
carrier correspondence, BEFORE imposing strongness.

In particular, selecting the first k vector levels is equivalent to
taking the first k+1 scalar source levels, including the newly added
common root. This is the finite-stem representation needed to
define a well-defined scalar colouring of ATR finite codes.

The strong-subtree bijection and arbitrary-tree Milliken A.4
remain separate proof obligations.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Root-glued source level zero is the new root; all later levels
are exactly the three coordinate levels, shifted up by one. -/
def selectedGluedLevels (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => f k + 1

@[simp] theorem selectedGluedLevels_zero (f : Nat → Nat) :
    selectedGluedLevels f 0 = 0 := rfl

@[simp] theorem selectedGluedLevels_succ (f : Nat → Nat) (k : Nat) :
    selectedGluedLevels f (k + 1) = f k + 1 := rfl

theorem selectedGluedLevels_strictMono
    (f : Nat → Nat) (hf : StrictMono f) :
    StrictMono (selectedGluedLevels f) := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero =>
      simp [selectedGluedLevels]
  | succ k =>
      change f k + 1 < f (k + 1) + 1
      exact Nat.add_lt_add_right (hf (Nat.lt_succ_self k)) 1

namespace TypedVectorSubset

/-- The first k selected source levels, with the same typed coordinates. -/
def truncateSelected (V : TypedVectorSubset)
    (f : Nat → Nat) (k : Nat) : TypedVectorSubset where
  carrier i := {x | x ∈ V.carrier i ∧
    ∃ j : Nat, j < k ∧ level x = f j}
  correctlyTyped := by
    intro i x hx
    exact V.correctlyTyped i x hx.1

theorem truncateSelected_mem_iff
    (V : TypedVectorSubset)
    (f : Nat → Nat) (k : Nat)
    (i : Fin 3) (x : CoordNode) :
    x ∈ (V.truncateSelected f k).carrier i ↔
      x ∈ V.carrier i ∧
        ∃ j : Nat, j < k ∧ level x = f j :=
  Iff.rfl

/-- The glued finite prefix reconstructs its three selected
coordinate slices *literally*, with no arbitrary representation. -/
theorem glue_truncateSelected_mem
    (V : TypedVectorSubset) (f : Nat → Nat) (k : Nat)
    (x : Option CoordNode) :
    x ∈ (V.truncateSelected f k).glue ↔
      x = none ∨
      ∃ y : CoordNode, x = some y ∧
        y ∈ V.union ∧
        ∃ j : Nat, j < k ∧
          gluedLevel x = selectedGluedLevels f (j + 1) := by
  cases x with
  | none =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        exact (V.truncateSelected f k).root_mem
  | some y =>
      rw [some_mem_iff]
      change
        (y ∈ V.carrier (sort y) ∧
          ∃ j : Nat, j < k ∧ level y = f j) ↔
          (some y = none ∨
          ∃ z : CoordNode, some y = some z ∧
            z ∈ V.union ∧
            ∃ j : Nat, j < k ∧
              gluedLevel (some y) = selectedGluedLevels f (j + 1))
      simp only [Option.some_ne_none, false_or]
      constructor
      · rintro ⟨hy, j, hj, hlevel⟩
        exact ⟨y, rfl, hy, j, hj, by simpa [hlevel]⟩
      · rintro ⟨z, h, hz, j, hj, hlevel⟩
        have heq : y = z := Option.some.inj h
        subst z
        exact ⟨hz, j, hj, by
          change level y + 1 = f j + 1 at hlevel
          omega⟩

/-- Exactly the first k+1 scalar source levels occur in the glued
finite prefix, assuming V has the chosen synchronized level map. -/
theorem glue_truncateSelected_levels
    (V : TypedVectorSubset) (f : Nat → Nat) (k : Nat)
    (x : Option CoordNode)
    (hx : x ∈ (V.truncateSelected f k).glue) :
    ∃ j : Nat, j < k + 1 ∧
      gluedLevel x = selectedGluedLevels f j := by
  cases x with
  | none =>
      exact ⟨0, Nat.zero_lt_succ k, rfl⟩
  | some x =>
      have hmem : x ∈ (V.truncateSelected f k).union :=
        ((V.truncateSelected f k).some_mem_iff x).mp hx
      obtain ⟨_, j, hj, hl⟩ := hmem
      exact ⟨j + 1, Nat.succ_lt_succ hj,
        by simpa [selectedGluedLevels] using congrArg Nat.succ hl⟩

end TypedVectorSubset
end CoordNode
end ThreeUniformDiaries
