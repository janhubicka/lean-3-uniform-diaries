import ThreeUniformDiaries.RootGluedReverseAncestors
import Milliken.GeneralTree.Ancestry

/-!
# Literal selected-ancestor closure of scalar-extracted ATR coordinates

A scalar strong subtree has selected ancestors by its no-ghost field.
In the genuine E0/E1/E2 type trees, any ancestor at a given ambient
level is exactly the unique type-record truncation at that level.

The extracted coordinate slices consequently contain the *literal*
truncation of each of their nodes at every earlier selected level.
This is not an assumption that scalar refinements are vector pictures;
it is an actual deduction needed in the converse gluing and meet proof.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem millikenCoordinate_selected_truncate_mem
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (i : Fin 3)
    (a b : Nat) (hab : a ≤ b)
    (x : CoordNode)
    (hx : x ∈ millikenCoordinateSlice S i)
    (hxlevel : level x = f b) :
    truncate x (f a) ∈ millikenCoordinateSlice S i := by
  have hslevel :
      rootGluedAmbientTree.level (some x : WithBot CoordNode) =
        S.levels (b + 1) := by
    rw [hlevels, selectedGluedLevels_succ]
    have hrank := rootGluedAmbient_level_coe x
    omega
  obtain ⟨z, hz, hzx⟩ :=
    S.exists_sourceLevel_ancestor (Nat.succ_le_succ hab)
      ⟨hx.2, hslevel⟩
  cases z with
  | none =>
      have hzlevel := hz.2
      rw [hlevels, selectedGluedLevels_succ] at hzlevel
      have hroot := rootGluedAmbientTree.level_root
      change rootGluedAmbientTree.level
        (none : WithBot CoordNode) = f a + 1 at hzlevel
      omega
  | some p =>
      have hplevel : level p = f a := by
        have hzlevel := hz.2
        rw [hlevels, selectedGluedLevels_succ] at hzlevel
        have hrank := rootGluedAmbient_level_coe p
        omega
      have hpx : p ≤ x := WithBot.coe_le_coe.mp hzx
      have htr : truncate x (f a) = p := by
        have hh := hpx.2
        rw [hplevel] at hh
        exact hh
      have hpsort : sort p = i :=
        (sort_eq_of_le hpx).trans hx.1
      rw [htr]
      exact ⟨hpsort, hz.1⟩

end CoordNode
end ThreeUniformDiaries
