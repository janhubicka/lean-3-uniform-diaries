import ThreeUniformDiaries.CoordinateTree

/-!
# Root-gluing the three non-homogeneous coordinate type trees

The scalar reduction in the ATR manuscript attaches a new root below
the three coordinate trees. On carriers, the gluing must keep track
of the coordinate sort; otherwise a tuple of three arbitrary subsets
cannot be recovered from their union.

This file formalises the exact typed carrier correspondence and
the one-level shift of all selected levels. It is the first step in
the root-gluing reduction of the variable-branching vector Milliken
theorem to a scalar non-homogeneous Milliken theorem.

The strong-subtree correspondence and the general non-homogeneous
Milliken theorem themselves are NOT claimed or postulated here.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Coordinate index: E0 = 0, E1 = 1, E2 = 2. -/
def sort : CoordNode → Fin 3
  | .enum _ _ => 0
  | .one _ _ => 1
  | .aux _ _ => 2

/-- A vector of sets using only nodes of its designated coordinate. -/
structure TypedVectorSubset where
  carrier : Fin 3 → Set CoordNode
  correctlyTyped : ∀ i (x : CoordNode),
    x ∈ carrier i → sort x = i

namespace TypedVectorSubset

/-- The three coordinate subsets as a single set in the forest. -/
def union (V : TypedVectorSubset) : Set CoordNode :=
  {x | x ∈ V.carrier (sort x)}

/-- Add one new common root below the typed disjoint union. -/
def glue (V : TypedVectorSubset) : Set (Option CoordNode) :=
  {x | x = none ∨ ∃ t : CoordNode, x = some t ∧ t ∈ V.union}

theorem root_mem (V : TypedVectorSubset) : none ∈ V.glue :=
  Or.inl rfl

theorem some_mem_iff (V : TypedVectorSubset) (x : CoordNode) :
    some x ∈ V.glue ↔ x ∈ V.union := by
  change (some x = none ∨
      ∃ t : CoordNode, some x = some t ∧ t ∈ V.union) ↔
    x ∈ V.union
  constructor
  · rintro (h | ⟨t, hxt, ht⟩)
    · cases h
    · have h : x = t := Option.some.inj hxt
      simpa only [h] using ht
  · intro hx
    exact Or.inr ⟨x, rfl, hx⟩

/-- Typed coordinate nodes are recovered literally from the glued set. -/
theorem mem_coordinate_iff_glued
    (V : TypedVectorSubset) (i : Fin 3) (x : CoordNode)
    (hxSort : sort x = i) :
    x ∈ V.carrier i ↔ some x ∈ V.glue := by
  rw [some_mem_iff, union, Set.mem_ofPred_eq, hxSort]

/-- Members of the wrong coordinate never occur in that coordinate set. -/
theorem not_mem_wrong_sort
    (V : TypedVectorSubset) (i : Fin 3) (x : CoordNode)
    (hxi : sort x ≠ i) :
    x ∉ V.carrier i := by
  intro hx
  exact hxi (V.correctlyTyped i x hx)

/-- The glued set determines the entire typed vector subset. -/
theorem glue_injective : Function.Injective glue := by
  intro V W hVW
  have hcoords : ∀ i, V.carrier i = W.carrier i := by
    intro i
    ext x
    by_cases hsort : sort x = i
    · have hiff : some x ∈ V.glue ↔ some x ∈ W.glue := by
        rw [hVW]
      exact (V.mem_coordinate_iff_glued i x hsort).trans
        (hiff.trans (W.mem_coordinate_iff_glued i x hsort).symm)
    · have hVnone := V.not_mem_wrong_sort i x hsort
      have hWnone := W.not_mem_wrong_sort i x hsort
      simp [hVnone, hWnone]
  cases V with
  | mk v hv =>
    cases W with
    | mk w hw =>
      congr 1
      funext i
      exact hcoords i

end TypedVectorSubset

/-- Shift levels by one after adding the new common root. -/
def gluedLevel : Option CoordNode → Nat
  | none => 0
  | some x => level x + 1

@[simp] theorem gluedLevel_root : gluedLevel none = 0 := rfl

@[simp] theorem gluedLevel_coord (x : CoordNode) :
    gluedLevel (some x) = level x + 1 := rfl

/-- If all three coordinate pictures occupy one common level map,
the glued picture occupies only level zero and its shifted levels. -/
theorem glued_selected_levels
    (V : TypedVectorSubset) (f : Nat → Nat)
    (hlevels : ∀ i (x : CoordNode), x ∈ V.carrier i →
      ∃ k : Nat, level x = f k) :
    ∀ x : Option CoordNode, x ∈ V.glue →
      x = none ∨ ∃ k : Nat, gluedLevel x = f k + 1 := by
  intro x hx
  cases x with
  | none => exact Or.inl rfl
  | some x =>
      right
      have hmem : x ∈ V.union :=
        (V.some_mem_iff x).mp hx
      obtain ⟨k, hk⟩ := hlevels (sort x) x hmem
      exact ⟨k, by simpa [hk]⟩

end CoordNode
end ThreeUniformDiaries
