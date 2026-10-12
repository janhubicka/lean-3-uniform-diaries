import ThreeUniformDiaries.RootGluedReverseCoordinate
import Milliken.GeneralTree.Ancestry

/-!
# Selected ancestry and level-population in the actual reverse ATR coordinates

A scalar Milliken refinement rooted at the added root splits into three
nonempty, pruned E0/E1/E2 coordinate slices. The chosen root of each
slice is below all its nodes, and every selected coordinate level is
nonempty. These facts are deductions from the *real* scalar strongness
axioms, not extra vector realization hypotheses.

Meet closure is handled separately; after that, together with the
checked next-child theorem, each slice is an InfiniteStrongPicture.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The unique first selected root in a coordinate cone is below
every retained node in that coordinate at any selected height. -/
theorem millikenCoordinate_firstRoot_le
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (t : CoordNode) (ht : level t = 0)
    (r : CoordNode)
    (hr : r ∈ millikenCoordinateSlice S (sort t) ∧
      level r = f 0)
    (x : CoordNode)
    (hx : x ∈ millikenCoordinateSlice S (sort t)) :
    r ≤ x := by
  obtain ⟨chosen, hchosen, hunique⟩ :=
    millikenCoordinate_unique_first_root S f hlevels t ht
  have hre : r = chosen := hunique r hr
  obtain ⟨m, hm⟩ := S.carrier_levels (some x : WithBot CoordNode) hx.2
  have hmpos : 1 ≤ m := by
    by_contra hnot
    have hmzero : m = 0 := by omega
    rw [hmzero, hlevels, selectedGluedLevels_zero] at hm
    have hrank := rootGluedAmbient_level_coe x
    omega
  obtain ⟨z, hz, hzx⟩ :=
    S.exists_sourceLevel_ancestor hmpos ⟨hx.2, hm⟩
  cases z with
  | none =>
      have hlevel := hz.2
      rw [hlevels, selectedGluedLevels_succ] at hlevel
      have hzero :=
        rootGluedAmbient_level_eq_gluedLevel (none : WithBot CoordNode)
      change rootGluedAmbientTree.level
        (none : WithBot CoordNode) = f 0 + 1 at hlevel
      omega
  | some p =>
      have hpsort : sort p = sort t := by
        have hpx : sort p = sort x :=
          sort_eq_of_le (WithBot.coe_le_coe.mp hzx)
        exact hpx.trans hx.1
      have hplevel : level p = f 0 := by
        have hlev := hz.2
        rw [hlevels, selectedGluedLevels_succ] at hlev
        have hrank := rootGluedAmbient_level_coe p
        omega
      have hpc : p = chosen :=
        hunique p ⟨⟨hpsort, hz.1⟩, hplevel⟩
      have hrp : r = p := hre.trans hpc.symm
      rw [hrp]
      exact WithBot.coe_le_coe.mp hzx

/-- Every retained node in a coordinate belongs to exactly one
positive selected scalar source level, hence to some true coordinate
level f(j). -/
theorem millikenCoordinate_selected_levels
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (i : Fin 3)
    (x : CoordNode)
    (hx : x ∈ millikenCoordinateSlice S i) :
    ∃ j : Nat, level x = f j := by
  obtain ⟨m, hm⟩ := S.carrier_levels (some x : WithBot CoordNode) hx.2
  cases m with
  | zero =>
      rw [hlevels, selectedGluedLevels_zero] at hm
      have hrank := rootGluedAmbient_level_coe x
      omega
  | succ j =>
      refine ⟨j, ?_⟩
      rw [hlevels, selectedGluedLevels_succ] at hm
      have hrank := rootGluedAmbient_level_coe x
      omega

/-- Every selected coordinate height is populated, including heights
arbitrarily far above the root, by repeatedly following actual
immediate-successor cones in that same coordinate. -/
theorem millikenCoordinate_all_levels
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (t : CoordNode) (ht : level t = 0)
    (j : Nat) :
    ∃ x : CoordNode,
      x ∈ millikenCoordinateSlice S (sort t) ∧
        level x = f j := by
  obtain ⟨r, hr, _⟩ :=
    millikenCoordinate_unique_first_root S f hlevels t ht
  induction j with
  | zero =>
      exact ⟨r, hr⟩
  | succ j ih =>
      obtain ⟨p, hp, hpLevel⟩ := ih
      obtain ⟨u, hu⟩ :=
        gluedChild_exists (some p : WithBot CoordNode)
      cases u with
      | none =>
          exact False.elim hu
      | some q =>
          have hpq : p ⋖ q := hu
          obtain ⟨z, hz, _⟩ :=
            millikenCoordinate_next_child S f hlevels
              (sort t) j p hp hpLevel q hpq
          exact ⟨z, hz.1, hz.2.1⟩

end CoordNode
end ThreeUniformDiaries
