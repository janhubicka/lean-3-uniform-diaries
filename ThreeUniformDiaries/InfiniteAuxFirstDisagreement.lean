import ThreeUniformDiaries.InfiniteAuxDistinctMeets
import ThreeUniformDiaries.DistinctParentDescendantMeets
import ThreeUniformDiaries.InfiniteCanonicalAuxOneRestriction
import ThreeUniformDiaries.InfiniteCanonicalInjectivity

/-!
# First-disagreement meet preservation for arbitrary finite auxiliary nodes

The genuine infinite auxiliary canonical map is known to send
DIFFERENT IMMEDIATE SOURCE CHILDREN into separate ambient
successor cones. We extend this fact from immediate children to
any two nodes at an arbitrary common source level N that first
disagree at index n < N.

The map of both full source nodes then meets exactly at the
canonical image of their common prefix at level n. This is the
essential non-consecutive-level case in the geometric meet-closure
step of the manuscript's canonical composition lemma.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxCanonicalMap_firstDisagreement_meet
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (hf : StrictMono f)
    {N n : Nat} (u v : AuxNode N) (hnN : n < N)
    (hcut : u.truncate n = v.truncate n)
    (hdiff : u.bit n ≠ v.bit n) :
    meet
      (.aux (f N) (infiniteAuxCanonicalMap hS N u).val)
      (.aux (f N) (infiniteAuxCanonicalMap hS N v).val) =
      .aux (f n)
        (infiniteAuxCanonicalMap hS n (u.truncate n)).val := by
  let p : CoordNode :=
    .aux (f n) (infiniteAuxCanonicalMap hS n (u.truncate n)).val
  let a : CoordNode :=
    .aux (f (n + 1))
      (infiniteAuxCanonicalMap hS (n + 1) (u.truncate (n + 1))).val
  let b : CoordNode :=
    .aux (f (n + 1))
      (infiniteAuxCanonicalMap hS (n + 1) (v.truncate (n + 1))).val
  let x : CoordNode :=
    .aux (f N) (infiniteAuxCanonicalMap hS N u).val
  let y : CoordNode :=
    .aux (f N) (infiniteAuxCanonicalMap hS N v).val
  have hsrcA :
      (u.truncate n).succ (u.bit n) = u.truncate (n + 1) := by
    have h := (u.truncate (n + 1)).succ_truncate_new
    rw [u.truncate_truncate (Nat.le_succ n)] at h
    have hb : (u.truncate (n + 1)).bit n = u.bit n := by
      simp [AuxNode.truncate, Nat.lt_succ_self]
    rw [hb] at h
    exact h
  have hsrcB :
      (u.truncate n).succ (v.bit n) = v.truncate (n + 1) := by
    rw [hcut]
    have h := (v.truncate (n + 1)).succ_truncate_new
    rw [v.truncate_truncate (Nat.le_succ n)] at h
    have hb : (v.truncate (n + 1)).bit n = v.bit n := by
      simp [AuxNode.truncate, Nat.lt_succ_self]
    rw [hb] at h
    exact h
  have hlocal :=
    infiniteAuxCanonicalMap_distinct_child_meet hS n
      (u.truncate n) (u.bit n) (v.bit n) hdiff
  rw [hsrcA, hsrcB] at hlocal
  have hpa : p ≤ a := by
    have htr := infiniteAuxCanonicalMap_truncate hS hf
      n (n + 1) (by omega) (u.truncate (n + 1))
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.aux (f n)
        ((infiniteAuxCanonicalMap hS (n + 1)
          (u.truncate (n + 1))).val.truncate (f n)) = p
    rw [htr, u.truncate_truncate (Nat.le_succ n)]
  have hpb : p ≤ b := by
    have htr := infiniteAuxCanonicalMap_truncate hS hf
      n (n + 1) (by omega) (v.truncate (n + 1))
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.aux (f n)
        ((infiniteAuxCanonicalMap hS (n + 1)
          (v.truncate (n + 1))).val.truncate (f n)) = p
    rw [htr, v.truncate_truncate (Nat.le_succ n), ← hcut]
  have hab : a ≠ b := by
    intro heq
    have hval :
        (infiniteAuxCanonicalMap hS (n + 1)
          (u.truncate (n + 1))).val =
        (infiniteAuxCanonicalMap hS (n + 1)
          (v.truncate (n + 1))).val := by
      injection heq
    have hsrc : u.truncate (n + 1) = v.truncate (n + 1) :=
      (infiniteAuxCanonicalMap_injective hS hf (n + 1)) hval
    have hb := congrArg (fun z : AuxNode (n + 1) => z.bit n) hsrc
    have hb' : u.bit n = v.bit n := by
      simpa [AuxNode.truncate, Nat.lt_succ_self] using hb
    exact hdiff hb'
  have hax : a ≤ x := by
    have htr := infiniteAuxCanonicalMap_truncate hS hf
      (n + 1) N (by omega) u
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.aux (f (n + 1))
        ((infiniteAuxCanonicalMap hS N u).val.truncate (f (n + 1))) = a
    rw [htr]
  have hby : b ≤ y := by
    have htr := infiniteAuxCanonicalMap_truncate hS hf
      (n + 1) N (by omega) v
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.aux (f (n + 1))
        ((infiniteAuxCanonicalMap hS N v).val.truncate (f (n + 1))) = b
    rw [htr]
  have hdesc :=
    meet_descendants_distinct_parents a b x y rfl hab
      hax hby ⟨p, hpa, hpb⟩
  change meet x y = p
  exact hdesc.trans hlocal

end CoordNode
end ThreeUniformDiaries
