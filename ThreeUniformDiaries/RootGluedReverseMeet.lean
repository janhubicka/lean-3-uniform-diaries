import ThreeUniformDiaries.RootGluedReverseTruncation
import ThreeUniformDiaries.RootGluedReverseFork
import ThreeUniformDiaries.CoordinateMeetTruncation

/-!
# Converse Milliken: actual E0/E1/E2 coordinate meet closure

The full scalar-to-vector correspondence must establish that each
coordinate slice of any actual rooted scalar Milliken strong subtree
is closed under the TRUE greatest-common-prefix meet of type records.

We first prove this at a fixed selected coordinate height by
induction on that height. Distinct immediate selected successors meet
at their common parent; distinct earlier selected ancestors let us
transport the meet to the shorter prefix. We then reduce mixed-height
pairs to the same-height theorem via literal selected truncation.

No assumption of a meet-preserving decoder or a vector-subtree model
is made here.
-/

namespace ThreeUniformDiaries
namespace CoordNode

private theorem meet_self_at_coord (x : CoordNode) :
    meet x x = x := by
  have hcommon : ∃ c : CoordNode, c ≤ x ∧ c ≤ x :=
    ⟨x, le_refl x, le_refl x⟩
  exact le_antisymm (meet_le_left hcommon)
    (le_meet (le_refl x) (le_refl x))

/-- Actual meet closure for any two coordinate nodes occupying
the SAME chosen source level of an arbitrary scalar Milliken subtree. -/
theorem millikenCoordinate_meet_same_level
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (hf : StrictMono f)
    (i : Fin 3) :
    ∀ (n : Nat) (x y : CoordNode),
      x ∈ millikenCoordinateSlice S i →
      level x = f n →
      y ∈ millikenCoordinateSlice S i →
      level y = f n →
      meet x y ∈ millikenCoordinateSlice S i := by
  intro n
  induction n with
  | zero =>
      intro x y hx hxLevel hy hyLevel
      let t := truncate x 0
      have ht : level t = 0 := by simp [t]
      have hsort : sort t = i :=
        (sort_truncate x 0).trans hx.1
      obtain ⟨r, hr, hu⟩ :=
        millikenCoordinate_unique_first_root S f hlevels t ht
      have hxs : x ∈ millikenCoordinateSlice S (sort t) := by
        rw [hsort]
        exact hx
      have hys : y ∈ millikenCoordinateSlice S (sort t) := by
        rw [hsort]
        exact hy
      have hxR : x = r := hu x ⟨hxs, hxLevel⟩
      have hyR : y = r := hu y ⟨hys, hyLevel⟩
      have hxy : x = y := hxR.trans hyR.symm
      rw [hxy, meet_self_at_coord]
      exact hy
  | succ n ih =>
      intro x y hx hxLevel hy hyLevel
      by_cases hxy : x = y
      · subst y
        rw [meet_self_at_coord]
        exact hx
      · let px := truncate x (f n)
        let py := truncate y (f n)
        have hstep : f n ≤ f (n + 1) :=
          (hf (Nat.lt_succ_self n)).le
        have hxBound : f n ≤ level x := by
          rw [hxLevel]
          exact hstep
        have hyBound : f n ≤ level y := by
          rw [hyLevel]
          exact hstep
        have hpx : px ∈ millikenCoordinateSlice S i :=
          millikenCoordinate_selected_truncate_mem S f hlevels
            i n (n + 1) (Nat.le_succ n) x hx hxLevel
        have hpy : py ∈ millikenCoordinateSlice S i :=
          millikenCoordinate_selected_truncate_mem S f hlevels
            i n (n + 1) (Nat.le_succ n) y hy hyLevel
        have hpxLevel : level px = f n := by
          simp only [px, level_truncate]
        have hpyLevel : level py = f n := by
          simp only [py, level_truncate]
        have hpxle : px ≤ x := truncate_le x hxBound
        have hpyle : py ≤ y := truncate_le y hyBound
        by_cases hpeq : px = py
        · have hpxy : px ≤ y := by
            rw [hpeq]
            exact hpyle
          have hmeet :=
            millikenCoordinate_distinct_next_meet S f hlevels
              i n px hpx hpxLevel x y
              hx hxLevel hpxle hy hyLevel hpxy hxy
          rw [hmeet]
          exact hpx
        · have hcommon : ∃ c : CoordNode, c ≤ x ∧ c ≤ y :=
            commonAncestor_of_same_sort x y
              (hx.1.trans hy.1.symm)
          have hmeet :
              meet x y = meet px py := by
            change meet x y =
              meet (truncate x (f n)) (truncate y (f n))
            exact meet_eq_meet_truncate_of_distinct
              x y (f n) hxBound hyBound hpeq hcommon
          rw [hmeet]
          exact ih px py hpx hpxLevel hpy hpyLevel

/-- Full actual coordinate meet closure, also for nodes on
DIFFERENT selected source levels. -/
theorem millikenCoordinate_meet_closed
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (f : Nat → Nat)
    (hlevels : S.levels = selectedGluedLevels f)
    (hf : StrictMono f)
    (i : Fin 3)
    (x y : CoordNode)
    (hx : x ∈ millikenCoordinateSlice S i)
    (hy : y ∈ millikenCoordinateSlice S i) :
    meet x y ∈ millikenCoordinateSlice S i := by
  obtain ⟨a, hxa⟩ :=
    millikenCoordinate_selected_levels S f hlevels i x hx
  obtain ⟨b, hyb⟩ :=
    millikenCoordinate_selected_levels S f hlevels i y hy
  have hcommon : ∃ c : CoordNode, c ≤ x ∧ c ≤ y :=
    commonAncestor_of_same_sort x y (hx.1.trans hy.1.symm)
  rcases le_total a b with hab | hba
  · let z := truncate y (f a)
    have hz : z ∈ millikenCoordinateSlice S i :=
      millikenCoordinate_selected_truncate_mem
        S f hlevels i a b hab y hy hyb
    have hzLevel : level z = f a := by simp [z]
    have hxSelf : truncate x (f a) = x := by
      rw [← hxa]
      exact truncate_self x
    by_cases heq : x = z
    · have hxy : x ≤ y := by
        refine ⟨by rw [hxa, hyb]; exact hf.monotone hab, ?_⟩
        rw [hxa]
        exact heq.symm
      have hmeet : meet x y = x :=
        le_antisymm (meet_le_left hcommon)
          (le_meet (le_refl x) hxy)
      rw [hmeet]
      exact hx
    · have hneq : truncate x (f a) ≠ truncate y (f a) := by
        rw [hxSelf]
        exact heq
      have hxBound : f a ≤ level x := by rw [hxa]
      have hyBound : f a ≤ level y := by
        rw [hyb]
        exact hf.monotone hab
      have hmeet :=
        meet_eq_meet_truncate_of_distinct x y
          (f a) hxBound hyBound hneq hcommon
      rw [hmeet, hxSelf]
      exact millikenCoordinate_meet_same_level
        S f hlevels hf i a x z hx hxa hz hzLevel
  · let z := truncate x (f b)
    have hz : z ∈ millikenCoordinateSlice S i :=
      millikenCoordinate_selected_truncate_mem
        S f hlevels i b a hba x hx hxa
    have hzLevel : level z = f b := by simp [z]
    have hySelf : truncate y (f b) = y := by
      rw [← hyb]
      exact truncate_self y
    by_cases heq : y = z
    · have hyx : y ≤ x := by
        refine ⟨by rw [hyb, hxa]; exact hf.monotone hba, ?_⟩
        rw [hyb]
        exact heq.symm
      have hmeet : meet x y = y :=
        le_antisymm (meet_le_right hcommon)
          (le_meet hyx (le_refl y))
      rw [hmeet]
      exact hy
    · have hneq : truncate x (f b) ≠ truncate y (f b) := by
        rw [hySelf]
        intro h
        exact heq h.symm
      have hxBound : f b ≤ level x := by
        rw [hxa]
        exact hf.monotone hba
      have hyBound : f b ≤ level y := by rw [hyb]
      have hmeet :=
        meet_eq_meet_truncate_of_distinct x y
          (f b) hxBound hyBound hneq hcommon
      rw [hmeet, hySelf]
      exact millikenCoordinate_meet_same_level
        S f hlevels hf i b z y hz hzLevel hy hyb

end CoordNode
end ThreeUniformDiaries
