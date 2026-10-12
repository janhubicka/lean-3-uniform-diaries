import ThreeUniformDiaries.CoordinateTree

/-!
# Exact meet transport under distinct common-level type truncations

Two E0/E1/E2 type records whose truncations disagree at ambient height
k already split strictly below that height. Their meet is therefore
exactly the meet of their k-truncations. This elementary lemma is
independent of strong-tree colouring and is the geometric induction
step needed for the reverse Milliken scalar/vector correspondence.

It uses the actual greatest-common-prefix `CoordNode.meet`, not an
abstract homomorphism or a postulated meet-preserving code.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem meet_eq_meet_truncate_of_distinct
    (x y : CoordNode)
    (k : Nat)
    (hkx : k ≤ level x)
    (hky : k ≤ level y)
    (hxy : truncate x k ≠ truncate y k)
    (hcommon : ∃ c : CoordNode, c ≤ x ∧ c ≤ y) :
    meet x y = meet (truncate x k) (truncate y k) := by
  have hmx : meet x y ≤ x := meet_le_left hcommon
  have hmy : meet x y ≤ y := meet_le_right hcommon
  have hmlevel : level (meet x y) < k := by
    by_contra hnot
    have hkl : k ≤ level (meet x y) := by omega
    have hxEq : truncate x k = truncate (meet x y) k := by
      calc
        truncate x k =
          truncate (truncate x (level (meet x y))) k :=
            (truncate_truncate x hkl).symm
        _ = truncate (meet x y) k := by rw [hmx.2]
    have hyEq : truncate y k = truncate (meet x y) k := by
      calc
        truncate y k =
          truncate (truncate y (level (meet x y))) k :=
            (truncate_truncate y hkl).symm
        _ = truncate (meet x y) k := by rw [hmy.2]
    exact hxy (hxEq.trans hyEq.symm)
  have hmTrX : meet x y ≤ truncate x k := by
    refine ⟨by simp only [level_truncate]; omega, ?_⟩
    change truncate (truncate x k) (level (meet x y)) = meet x y
    rw [truncate_truncate x (by omega)]
    exact hmx.2
  have hmTrY : meet x y ≤ truncate y k := by
    refine ⟨by simp only [level_truncate]; omega, ?_⟩
    change truncate (truncate y k) (level (meet x y)) = meet x y
    rw [truncate_truncate y (by omega)]
    exact hmy.2
  have hcommonTr : ∃ c : CoordNode,
      c ≤ truncate x k ∧ c ≤ truncate y k :=
    ⟨meet x y, hmTrX, hmTrY⟩
  apply le_antisymm
  · exact le_meet hmTrX hmTrY
  · apply le_meet
    · exact (meet_le_left hcommonTr).trans (truncate_le x hkx)
    · exact (meet_le_right hcommonTr).trans (truncate_le y hky)

end CoordNode
end ThreeUniformDiaries
