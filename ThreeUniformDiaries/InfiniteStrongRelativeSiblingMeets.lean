import ThreeUniformDiaries.InfiniteStrongRelativeLevels
import ThreeUniformDiaries.DistinctParentDescendantMeets

/-!
# Relative child cones meet exactly at their common retained parent

Distinct immediate child cones of a strong coordinate picture U are
separated at *selected* ambient levels. Their ambient meet need not
be controlled by immediate-child lemmas of the full type tree, since
U may skip many ambient levels.

We prove that distinct U-nodes at consecutive relative levels,
above the same retained parent p, meet precisely at p. The key is
meet-closure inside U: their meet is a U-node, hence cannot be
on a level strictly between f i and f(i+1).

The descendant version is the missing equal-parent/different-child
case for proving meet closure of the relative protected layer union.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Distinct selected children one relative level above p meet
precisely at p, even across arbitrary ambient-level gaps. -/
theorem infiniteStrongPicture_relative_siblings_meet
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f)
    (i : Nat) (p t u : CoordNode)
    (hpU : p ∈ U) (htU : t ∈ U) (huU : u ∈ U)
    (hpLevel : level p = f i)
    (htLevel : level t = f (i + 1))
    (huLevel : level u = f (i + 1))
    (hpt : p ≤ t) (hpu : p ≤ u)
    (htu : t ≠ u) :
    meet t u = p := by
  have hc : ∃ r : CoordNode, r ≤ t ∧ r ≤ u :=
    ⟨p, hpt, hpu⟩
  have hmU : meet t u ∈ U := hU.meet_closed htU huU
  obtain ⟨j, hlevel⟩ := hU.selected_levels (meet t u) hmU
  have hpMeet : p ≤ meet t u := le_meet hpt hpu
  have hmT : meet t u ≤ t := meet_le_left hc
  have hmU' : meet t u ≤ u := meet_le_right hc
  have hstrictLevel : level (meet t u) < level t := by
    have hle := level_le_of_le hmT
    by_contra hnot
    have heqLev : level (meet t u) = level t := by omega
    have heqT : meet t u = t :=
      eq_of_le_of_level_eq hmT heqLev
    have heqU : meet t u = u :=
      eq_of_le_of_level_eq hmU'
        (heqLev.trans (htLevel.trans huLevel.symm))
    exact htu (heqT.symm.trans heqU)
  have hiLeJ : i ≤ j := by
    by_contra hnot
    have hji : j < i := Nat.lt_of_not_ge hnot
    have hmono := hf hji
    have hle := level_le_of_le hpMeet
    rw [hpLevel, hlevel] at hle
    omega
  have hjLeI : j ≤ i := by
    by_contra hnot
    have hji : i < j := Nat.lt_of_not_ge hnot
    have hbound : i + 1 ≤ j := by omega
    have hmono := hf.monotone hbound
    rw [hlevel, htLevel] at hstrictLevel
    omega
  have hji : j = i := by omega
  have hEqLevels : level p = level (meet t u) := by
    rw [hpLevel, hlevel, hji]
  exact (eq_of_le_of_level_eq hpMeet hEqLevels).symm

/-- The same exact meet persists for all descendants of two
distinct relative child cones above one retained parent. -/
theorem infiniteStrongPicture_relative_sibling_descendant_meet
    {U : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hU : InfiniteStrongPicture U f root)
    (hf : StrictMono f)
    (i : Nat) (p t u x y : CoordNode)
    (hpU : p ∈ U) (htU : t ∈ U) (huU : u ∈ U)
    (hpLevel : level p = f i)
    (htLevel : level t = f (i + 1))
    (huLevel : level u = f (i + 1))
    (hpt : p ≤ t) (hpu : p ≤ u) (htu : t ≠ u)
    (htx : t ≤ x) (huy : u ≤ y) :
    meet x y = p := by
  have hsame : level t = level u :=
    htLevel.trans huLevel.symm
  have hcommon : ∃ r : CoordNode, r ≤ t ∧ r ≤ u :=
    ⟨p, hpt, hpu⟩
  calc
    meet x y = meet t u :=
      meet_descendants_distinct_parents t u x y
        hsame htu htx huy hcommon
    _ = p :=
      infiniteStrongPicture_relative_siblings_meet hU hf
        i p t u hpU htU huU hpLevel htLevel huLevel hpt hpu htu

end CoordNode
end ThreeUniformDiaries
