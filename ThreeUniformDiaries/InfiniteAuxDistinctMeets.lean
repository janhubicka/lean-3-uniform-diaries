import ThreeUniformDiaries.InfiniteCanonicalSuccessor
import ThreeUniformDiaries.DistinctChildConeMeets
import ThreeUniformDiaries.VectorTree

/-!
# Distinct source children in the genuine infinite auxiliary map

The concrete infinite auxiliary canonical map takes source bit-0
and bit-1 successors into different *immediate ambient successor
cones* of their common selected parent.  Therefore their images
meet EXACTLY at that parent, including arbitrary gaps in selected
ambient levels. The proof uses the already verified geometric
successor-cone laws and the general distinct-cone meet theorem.

This is the first local geometric step toward meeting the
strong-subtree composition obligation, without postulating
meet preservation as part of an abstract CanonicalMap.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxCanonicalMap_distinct_child_meet
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (n : Nat) (a : AuxNode n)
    (b c : Bool) (hbc : b ≠ c) :
    meet
      (.aux (f (n + 1))
        (infiniteAuxCanonicalMap hS (n + 1) (a.succ b)).val)
      (.aux (f (n + 1))
        (infiniteAuxCanonicalMap hS (n + 1) (a.succ c)).val)
      =
      .aux (f n) (infiniteAuxCanonicalMap hS n a).val := by
  let q := (infiniteAuxCanonicalMap hS n a).val
  let p : CoordNode := .aux (f n) q
  let t : CoordNode := .aux (f n + 1) (q.succ b)
  let u : CoordNode := .aux (f n + 1) (q.succ c)
  let x : CoordNode :=
    .aux (f (n + 1))
      (infiniteAuxCanonicalMap hS (n + 1) (a.succ b)).val
  let y : CoordNode :=
    .aux (f (n + 1))
      (infiniteAuxCanonicalMap hS (n + 1) (a.succ c)).val
  have hpt : p ≤ t := by
    refine ⟨Nat.le_succ _, ?_⟩
    change CoordNode.aux (f n) ((q.succ b).truncate (f n)) = p
    simp [p]
  have hpu : p ≤ u := by
    refine ⟨Nat.le_succ _, ?_⟩
    change CoordNode.aux (f n) ((q.succ c).truncate (f n)) = p
    simp [p]
  have hcovt : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
    rfl
  have hcovu : p ⋖ u := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpu
    rfl
  have htu : t ≠ u := by
    intro h
    change CoordNode.aux (f n + 1) (q.succ b) =
      CoordNode.aux (f n + 1) (q.succ c) at h
    have heq : q.succ b = q.succ c := by
      injection h
    have hbiteq : b = c := by
      have hv := congrArg
        (fun z : AuxNode (f n + 1) => z.bit (f n)) heq
      simpa using hv
    exact hbc hbiteq
  have htx : t ≤ x := infiniteAuxCanonicalMap_succ hS n a b
  have huy : u ≤ y := infiniteAuxCanonicalMap_succ hS n a c
  exact meet_descendants_distinct_children
    p t u x y hcovt hcovu htu htx huy

end CoordNode
end ThreeUniformDiaries
