import ThreeUniformDiaries.DistinctChildConeMeets

/-!
# Meets of descendants with distinct same-level selected parents

If p and q are different selected nodes on the same level, then
any descendants x>=p and y>=q have the same meet as p and q.
This is the complementary case to the different-child
same-parent formula and is crucial for proving meet-closure
of a union of strong-completion layers.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Passing to descendants of two distinct same-level parents does
not create a new meet above the previous selected level. -/
theorem meet_descendants_distinct_parents
    (p q x y : CoordNode)
    (hlevel : level p = level q) (hne : p ≠ q)
    (hpx : p ≤ x) (hqy : q ≤ y)
    (hcommon : ∃ r : CoordNode, r ≤ p ∧ r ≤ q) :
    meet x y = meet p q := by
  let z := meet x y
  have hcommonxy : ∃ r : CoordNode, r ≤ x ∧ r ≤ y := by
    rcases hcommon with ⟨r, hrp, hrq⟩
    exact ⟨r, le_trans hrp hpx, le_trans hrq hqy⟩
  have hzx : z ≤ x := meet_le_left hcommonxy
  have hzy : z ≤ y := meet_le_right hcommonxy
  have hzlow : level z < level p := by
    by_contra hnot
    have hple : level p ≤ level z := Nat.le_of_not_gt hnot
    have hpz : p ≤ z := by
      rcases lower_linear hpx hzx with hpz | hzp
      · exact hpz
      · have heqlev : level z = level p :=
          Nat.le_antisymm (level_le_of_le hzp) hple
        have hEq : z = p :=
          eq_of_le_of_level_eq hzp heqlev
        exact le_of_eq hEq.symm
    have hqle : level q ≤ level z := by
      rw [← hlevel]
      exact hple
    have hqz : q ≤ z := by
      rcases lower_linear hqy hzy with hqz | hzq
      · exact hqz
      · have heqlev : level z = level q :=
          Nat.le_antisymm (level_le_of_le hzq) hqle
        have hEq : z = q :=
          eq_of_le_of_level_eq hzq heqlev
        exact le_of_eq hEq.symm
    exact no_common_upper_same_level p q hlevel hne
      ⟨z, hpz, hqz⟩
  have hzqLow : level z < level q := by
    rw [← hlevel]
    exact hzlow
  have hzp : z ≤ p := by
    rcases lower_linear hzx hpx with hzp | hpz
    · exact hzp
    · have hl := level_le_of_le hpz
      omega
  have hzq : z ≤ q := by
    rcases lower_linear hzy hqy with hzq | hqz
    · exact hzq
    · have hl := level_le_of_le hqz
      omega
  have hmeetsource : meet p q ≤ z := by
    have hp := meet_le_left hcommon
    have hq := meet_le_right hcommon
    exact le_meet (le_trans hp hpx) (le_trans hq hqy)
  have hmeetdest : z ≤ meet p q := le_meet hzp hzq
  exact le_antisymm hmeetdest hmeetsource

end CoordNode
end ThreeUniformDiaries
