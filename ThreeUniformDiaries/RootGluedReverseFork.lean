import ThreeUniformDiaries.RootGluedReverseCoordinate

/-!
# Fork rigidity in an arbitrary scalar Milliken refinement of E0/E1/E2

At each selected coordinate level, distinct retained successors of
the same retained type-record parent have that parent as their
*actual* greatest common prefix in the ambient type tree.

The proof uses the real immediate successor at one ambient level
after the alleged common prefix and the checked one-per-cone scalar
strongness, not a postulated meet-closure axiom. This is an essential
local ingredient in the complete scalar-to-vector converse.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Distinct retained nodes at the next chosen coordinate level
above the same selected parent meet exactly at that parent. -/
theorem millikenCoordinate_distinct_next_meet
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (i : Fin 3) (j : Nat)
    (p : CoordNode)
    (hp : p ∈ millikenCoordinateSlice S i)
    (hpLevel : level p = f j)
    (x y : CoordNode)
    (hx : x ∈ millikenCoordinateSlice S i)
    (hxLevel : level x = f (j + 1))
    (hpx : p ≤ x)
    (hy : y ∈ millikenCoordinateSlice S i)
    (hyLevel : level y = f (j + 1))
    (hpy : p ≤ y)
    (hxy : x ≠ y) :
    meet x y = p := by
  have hcommon : ∃ z : CoordNode, z ≤ x ∧ z ≤ y :=
    ⟨p, hpx, hpy⟩
  have hpm : p ≤ meet x y := le_meet hpx hpy
  by_contra hne
  have hlt : p < meet x y :=
    lt_of_le_of_ne hpm (Ne.symm hne)
  have hlevel : level p + 1 ≤ level (meet x y) := by
    have hh := level_lt_of_lt hlt
    omega
  let t : CoordNode := truncate (meet x y) (level p + 1)
  have htLevel : level t = level p + 1 := by
    simp only [t, level_truncate]
  have hptle : p ≤ t := by
    refine ⟨by rw [htLevel]; omega, ?_⟩
    change truncate (truncate (meet x y) (level p + 1))
      (level p) = p
    rw [truncate_truncate _ (Nat.le_succ (level p))]
    exact hpm.2
  have hpt : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hptle
    exact htLevel
  have htm : t ≤ meet x y :=
    truncate_le _ hlevel
  have htx : t ≤ x :=
    htm.trans (meet_le_left hcommon)
  have hty : t ≤ y :=
    htm.trans (meet_le_right hcommon)
  obtain ⟨q, _, hu⟩ :=
    millikenCoordinate_next_child S f hlevels i
      j p hp hpLevel t hpt
  have hxq : x = q :=
    hu x ⟨hx, hxLevel, htx⟩
  have hyq : y = q :=
    hu y ⟨hy, hyLevel, hty⟩
  exact hxy (hxq.trans hyq.symm)

end CoordNode
end ThreeUniformDiaries
