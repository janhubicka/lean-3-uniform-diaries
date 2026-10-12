import ThreeUniformDiaries.RootGluedZeroLevelRigidity

/-!
# The actual meet-semilattice of the root-glued type forest

The extra scalar root is the meet of nodes belonging to distinct
coordinates. Within a coordinate, the meet is the verified greatest
common prefix of its E0/E1/E2 type nodes. We work in `WithBot CoordNode`,
the order-theoretic bottom-extension of the actual coordinate forest;
this is canonically equivalent to the previously used Option carrier.

All meet laws are proved from genuine prefix meets. The further
predecessor/RootedTree packaging is a separate obligation.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Same-coordinate nodes have a common level-zero ancestor. -/
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

/-- The actual greatest common ancestor in the bottom-extended
root-glued forest. -/
noncomputable def rootGluedMeet
    (a b : WithBot CoordNode) : WithBot CoordNode :=
  WithBot.recBotCoe (⊥ : WithBot CoordNode)
    (fun x => WithBot.recBotCoe (⊥ : WithBot CoordNode)
      (fun y => if sort x = sort y then
        (meet x y : WithBot CoordNode) else ⊥) b) a

theorem rootGluedMeet_le_left (a b : WithBot CoordNode) :
    rootGluedMeet a b ≤ a := by
  cases a with
  | bot => exact bot_le
  | coe x =>
      cases b with
      | bot => exact bot_le
      | coe y =>
          by_cases hxy : sort x = sort y
          · change (if sort x = sort y then
                (meet x y : WithBot CoordNode) else ⊥) ≤
                (x : WithBot CoordNode)
            rw [if_pos hxy]
            exact WithBot.coe_le_coe.mpr
              (meet_le_left (commonAncestor_of_same_sort x y hxy))
          · change (if sort x = sort y then
                (meet x y : WithBot CoordNode) else ⊥) ≤
                (x : WithBot CoordNode)
            rw [if_neg hxy]
            exact bot_le

theorem rootGluedMeet_le_right (a b : WithBot CoordNode) :
    rootGluedMeet a b ≤ b := by
  cases a with
  | bot => exact bot_le
  | coe x =>
      cases b with
      | bot => exact bot_le
      | coe y =>
          by_cases hxy : sort x = sort y
          · change (if sort x = sort y then
                (meet x y : WithBot CoordNode) else ⊥) ≤
                (y : WithBot CoordNode)
            rw [if_pos hxy]
            exact WithBot.coe_le_coe.mpr
              (meet_le_right (commonAncestor_of_same_sort x y hxy))
          · change (if sort x = sort y then
                (meet x y : WithBot CoordNode) else ⊥) ≤
                (y : WithBot CoordNode)
            rw [if_neg hxy]
            exact bot_le

theorem rootGluedMeet_greatest
    (a b c : WithBot CoordNode)
    (hca : c ≤ a) (hcb : c ≤ b) :
    c ≤ rootGluedMeet a b := by
  cases c with
  | bot =>
      exact bot_le
  | coe z =>
      cases a with
      | bot =>
          exact False.elim ((WithBot.not_coe_le_bot z) hca)
      | coe x =>
          cases b with
          | bot =>
              exact False.elim ((WithBot.not_coe_le_bot z) hcb)
          | coe y =>
              have hzx : z ≤ x := WithBot.coe_le_coe.mp hca
              have hzy : z ≤ y := WithBot.coe_le_coe.mp hcb
              have hxy : sort x = sort y :=
                (sort_eq_of_le hzx).symm.trans (sort_eq_of_le hzy)
              change (z : WithBot CoordNode) ≤
                (if sort x = sort y then
                  (meet x y : WithBot CoordNode) else ⊥)
              rw [if_pos hxy]
              exact WithBot.coe_le_coe.mpr (le_meet hzx hzy)

/-- The actual global meet of the glued, nonuniformly branching tree. -/
noncomputable instance : SemilatticeInf (WithBot CoordNode) where
  inf := rootGluedMeet
  inf_le_left := rootGluedMeet_le_left
  inf_le_right := rootGluedMeet_le_right
  le_inf := by
    intro a b c hab hac
    exact rootGluedMeet_greatest b c a hab hac

/-- Nodes from distinct coordinates meet precisely at the added root. -/
theorem rootGluedMeet_different_sorts
    (x y : CoordNode) (h : sort x ≠ sort y) :
    ((x : WithBot CoordNode) ⊓ (y : WithBot CoordNode)) = ⊥ := by
  change (if sort x = sort y then
    (meet x y : WithBot CoordNode) else ⊥) = ⊥
  simp [h]

/-- Within a coordinate the scalar meet is exactly the prefix meet. -/
theorem rootGluedMeet_same_sort
    (x y : CoordNode) (h : sort x = sort y) :
    ((x : WithBot CoordNode) ⊓ (y : WithBot CoordNode)) =
      (meet x y : WithBot CoordNode) := by
  change (if sort x = sort y then
    (meet x y : WithBot CoordNode) else ⊥) =
      (meet x y : WithBot CoordNode)
  simp [h]

end CoordNode
end ThreeUniformDiaries
