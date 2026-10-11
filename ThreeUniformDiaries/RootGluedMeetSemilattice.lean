import ThreeUniformDiaries.RootGluedZeroLevelRigidity

/-!
# The actual meet-semilattice of the root-glued type forest

The added scalar root is the meet of nodes belonging to different
coordinates. Within one coordinate, the meet is the actual prefix
meet already verified for E0/E1/E2. There is no new representative:
the meet remains the greatest common predecessor in the glued
ancestry order, even with unbounded branching at later levels.

These are the SemilatticeInf axioms required for Mathlib RootedTree
and thus for the new Milliken.GeneralTree.AmbientTree instance.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Two nodes of the same type-tree sort have their common
level-zero predecessor, so the original forest meet is valid. -/
theorem commonAncestor_of_same_sort
    (x y : CoordNode) (hxy : sort x = sort y) :
    ∃ c : CoordNode, c ≤ x ∧ c ≤ y := by
  let c := truncate x 0
  have hcX : c ≤ x := truncate_le x (Nat.zero_le _)
  have hcY : c = truncate y 0 := by
    apply unique_zero_node_of_same_sort
    · simp [c]
    · simp
    · dsimp only [c]
      rw [sort_truncate x 0, sort_truncate y 0]
      exact hxy
  refine ⟨c, hcX, ?_⟩
  rw [hcY]
  exact truncate_le y (Nat.zero_le _)

/-- The scalar meet: the new root joins different coordinate
types, whereas same-sort nodes use their exact old prefix meet. -/
noncomputable def rootGluedMeet :
    WithBot CoordNode → WithBot CoordNode
  | none, _ => none
  | _, none => none
  | some x, some y =>
      if sort x = sort y then some (meet x y) else none

theorem rootGluedMeet_le_left (a b : WithBot CoordNode) :
    rootGluedMeet a b ≤ a := by
  cases a with
  | none =>
      exact bot_le
  | some x =>
      cases b with
      | none => exact bot_le
      | some y =>
          by_cases hxy : sort x = sort y
          · change (if sort x = sort y then
                (some (meet x y) : WithBot CoordNode) else none) ≤ some x
            rw [if_pos hxy]
            change meet x y ≤ x
            exact meet_le_left (commonAncestor_of_same_sort x y hxy)
          · change (if sort x = sort y then
                (some (meet x y) : WithBot CoordNode) else none) ≤ some x
            rw [if_neg hxy]
            exact bot_le

theorem rootGluedMeet_le_right (a b : WithBot CoordNode) :
    rootGluedMeet a b ≤ b := by
  cases a with
  | none => exact bot_le
  | some x =>
      cases b with
      | none => exact bot_le
      | some y =>
          by_cases hxy : sort x = sort y
          · change (if sort x = sort y then
                (some (meet x y) : WithBot CoordNode) else none) ≤ some y
            rw [if_pos hxy]
            change meet x y ≤ y
            exact meet_le_right (commonAncestor_of_same_sort x y hxy)
          · change (if sort x = sort y then
                (some (meet x y) : WithBot CoordNode) else none) ≤ some y
            rw [if_neg hxy]
            exact bot_le

theorem rootGluedMeet_greatest
    (a b c : WithBot CoordNode)
    (hca : c ≤ a) (hcb : c ≤ b) :
    c ≤ rootGluedMeet a b := by
  cases c with
  | none =>
      exact bot_le
  | some z =>
      cases a with
      | none =>
          exact False.elim ((WithBot.not_coe_le_bot z) hca)
      | some x =>
          cases b with
          | none =>
              exact False.elim ((WithBot.not_coe_le_bot z) hcb)
          | some y =>
              have hzx : z ≤ x := hca
              have hzy : z ≤ y := hcb
              have hxy : sort x = sort y :=
                (sort_eq_of_le hzx).symm.trans (sort_eq_of_le hzy)
              change (some z : WithBot CoordNode) ≤
                (if sort x = sort y then
                  (some (meet x y) : WithBot CoordNode) else none)
              rw [if_pos hxy]
              change z ≤ meet x y
              exact le_meet hzx hzy

/-- The real global meet order of the glued type tree. -/
noncomputable instance : SemilatticeInf (WithBot CoordNode) where
  inf := rootGluedMeet
  inf_le_left := rootGluedMeet_le_left
  inf_le_right := rootGluedMeet_le_right
  le_inf := rootGluedMeet_greatest

/-- Distinct coordinate sorts meet at the added scalar root. -/
theorem rootGluedMeet_different_sorts
    (x y : CoordNode) (h : sort x ≠ sort y) :
    ((some x : WithBot CoordNode) ⊓ some y) = ⊥ := by
  change (if sort x = sort y then
    (some (meet x y) : WithBot CoordNode) else none) = none
  simp [h]

/-- Inside one coordinate the scalar meet agrees with its old
ambient tree-of-types meet, not a chosen proxy. -/
theorem rootGluedMeet_same_sort
    (x y : CoordNode) (h : sort x = sort y) :
    ((some x : WithBot CoordNode) ⊓ some y) = some (meet x y) := by
  change (if sort x = sort y then
    (some (meet x y) : WithBot CoordNode) else none) =
      some (meet x y)
  simp [h]

end CoordNode
end ThreeUniformDiaries
