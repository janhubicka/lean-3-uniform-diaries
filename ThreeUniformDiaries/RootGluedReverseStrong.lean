import ThreeUniformDiaries.RootGluedReverseMeet
import ThreeUniformDiaries.RootGluedLevelNormalization
import ThreeUniformDiaries.InfiniteCanonicalAux

/-!
# Reverse root-gluing into genuine infinite ATR strong coordinates

For every actual scalar strong subtree returned by a future arbitrary-
branching Milliken theorem, the three extracted E0/E1/E2 type-tree
slices satisfy ALL fields of InfiniteStrongPicture: selected root,
root ancestry, true type-tree meet closure, selected-level population
and uniqueness in each actual immediate child cone.

This is a converse theorem about the real glued ambient tree, not an
extra hypothesis postulating the desired vector representation.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A component of a scalar Milliken strong tree is itself a genuine
ATR geometric infinite strong picture in the original type tree. -/
theorem millikenCoordinate_exists_infiniteStrong
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (hf : StrictMono f)
    (t : CoordNode) (ht : level t = 0) :
    ∃ r : CoordNode,
      sort r = sort t ∧
        level r = f 0 ∧
        InfiniteStrongPicture
          (millikenCoordinateSlice S (sort t)) f r := by
  obtain ⟨r, ⟨hrmem, hrlev⟩, _⟩ :=
    millikenCoordinate_unique_first_root S f hlevels t ht
  refine ⟨r, hrmem.1, hrlev, ?_⟩
  exact {
    root_mem := hrmem
    root_le := by
      intro x hx
      exact millikenCoordinate_firstRoot_le
        S f hlevels t ht r ⟨hrmem, hrlev⟩ x hx
    meet_closed := by
      intro x y hx hy
      exact millikenCoordinate_meet_closed
        S f hlevels hf (sort t) x y hx hy
    selected_levels := by
      intro x hx
      exact millikenCoordinate_selected_levels S f hlevels (sort t) x hx
    all_levels := by
      intro i
      exact millikenCoordinate_all_levels S f hlevels t ht i
    next_child := by
      intro i p hp hpLevel z hpz
      exact millikenCoordinate_next_child
        S f hlevels (sort t) i p hp hpLevel z hpz
  }

/-- The actual scalar root automatically supplies the synchronized
coordinate level map, and then each chosen zero-level coordinate
cone yields a genuine InfiniteStrongPicture. -/
theorem millikenCoordinate_exists_infiniteStrong_of_root
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (hroot : S.root = (none : WithBot CoordNode))
    (t : CoordNode) (ht : level t = 0) :
    ∃ r : CoordNode,
      sort r = sort t ∧
        level r = millikenCoordinateLevels S 0 ∧
        InfiniteStrongPicture
          (millikenCoordinateSlice S (sort t))
          (millikenCoordinateLevels S) r := by
  let f := millikenCoordinateLevels S
  exact millikenCoordinate_exists_infiniteStrong S f
    (millikenLevels_eq_selectedGluedLevels S
      (millikenStrong_levels_zero_of_root S hroot))
    (millikenCoordinateLevels_strictMono S
      (millikenStrong_levels_zero_of_root S hroot))
    t ht

end CoordNode
end ThreeUniformDiaries
