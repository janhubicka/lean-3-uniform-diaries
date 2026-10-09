import ThreeUniformDiaries.CoordinateTree

/-!
# Meets across distinct immediate-successor cones

The strong-subtree completion inserts nodes in previously missing
successor directions. The new nodes must meet old nodes from another
direction at their common parent, exactly as in the ambient tree.
This lemma is uniform for enumeration, singleton and auxiliary
type-tree components.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Distinct nodes at one ambient level cannot have a common upper
node in the prefix tree. -/
theorem no_common_upper_same_level
    (a b : CoordNode)
    (hlev : level a = level b) (hne : a ≠ b) :
    ¬ ∃ z : CoordNode, a ≤ z ∧ b ≤ z := by
  rintro ⟨z, haz, hbz⟩
  rcases lower_linear haz hbz with hab | hba
  · exact hne (eq_of_le_of_level_eq hab hlev)
  · exact hne (eq_of_le_of_level_eq hba hlev.symm).symm

/-- Two different children of p generate disjoint upper cones. -/
theorem distinct_children_no_common_upper
    (p a b : CoordNode) (hpa : p ⋖ a) (hpb : p ⋖ b)
    (hne : a ≠ b) :
    ¬ ∃ z : CoordNode, a ≤ z ∧ b ≤ z := by
  have hlev : level a = level b := by
    rw [covBy_level hpa, covBy_level hpb]
  exact no_common_upper_same_level a b hlev hne

/-- For two descendants of distinct immediate successors of p, the
meet is exactly p (not merely at the level of p). -/
theorem meet_descendants_distinct_children
    (p a b x y : CoordNode)
    (hpa : p ⋖ a) (hpb : p ⋖ b)
    (hne : a ≠ b)
    (hax : a ≤ x) (hby : b ≤ y) :
    meet x y = p := by
  have hpx : p ≤ x := le_trans hpa.le hax
  have hpy : p ≤ y := le_trans hpb.le hby
  have hc : ∃ c : CoordNode, c ≤ x ∧ c ≤ y :=
    ⟨p, hpx, hpy⟩
  have hpq : p ≤ meet x y := le_meet hpx hpy
  have hqx : meet x y ≤ x := meet_le_left hc
  have hqy : meet x y ≤ y := meet_le_right hc
  by_contra hneq
  have hneq' : p ≠ meet x y := Ne.symm hneq
  have hlt : p < meet x y := lt_of_le_of_ne hpq hneq'
  have hlevel : level p < level (meet x y) := level_lt_of_lt hlt
  have haq : level a ≤ level (meet x y) := by
    rw [covBy_level hpa]
    omega
  have hbq : level b ≤ level (meet x y) := by
    rw [covBy_level hpb]
    omega
  have ha_meet : a ≤ meet x y := by
    rcases lower_linear hax hqx with h | h
    · exact h
    · have hl : level (meet x y) = level a := by
        apply Nat.le_antisymm
        · exact level_le_of_le h
        · exact haq
      have heq : meet x y = a :=
        eq_of_le_of_level_eq h hl
      exact le_of_eq heq.symm
  have hb_meet : b ≤ meet x y := by
    rcases lower_linear hby hqy with h | h
    · exact h
    · have hl : level (meet x y) = level b := by
        apply Nat.le_antisymm
        · exact level_le_of_le h
        · exact hbq
      have heq : meet x y = b :=
        eq_of_le_of_level_eq h hl
      exact le_of_eq heq.symm
  exact distinct_children_no_common_upper p a b hpa hpb hne
    ⟨meet x y, ha_meet, hb_meet⟩

end CoordNode
end ThreeUniformDiaries
