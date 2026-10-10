import ThreeUniformDiaries.InfiniteOneEnumDistinctMeets
import ThreeUniformDiaries.DistinctParentDescendantMeets
import ThreeUniformDiaries.InfiniteCanonicalAuxOneRestriction
import ThreeUniformDiaries.InfiniteCanonicalInjectivity

/-!
# First-disagreement meet preservation for arbitrary singleton-type nodes

The genuine infinite singleton canonical map is known to send
DIFFERENT IMMEDIATE SOURCE CHILDREN into separate ambient
successor cones. We extend this fact from immediate children to
two nodes at possibly different source levels N and M that first
disagree at an index n below both levels.

The map of both full source nodes then meets exactly at the
canonical singleton image of their common prefix at level n. This is the
essential non-consecutive-level case in the geometric meet-closure
step of the manuscript's canonical composition lemma.
-/

namespace ThreeUniformDiaries

namespace OneNode
/-- Boundary auxiliary parameter is unaffected by truncating
the singleton node just after the boundary index. -/
theorem boundaryAux_truncate_next {N : Nat} (a : OneNode N) (n : Nat) :
    (a.truncate (n + 1)).boundaryAux n = a.boundaryAux n := by
  apply AuxNode.ext_bits
  funext i
  by_cases hi : i < n
  · simp [OneNode.boundaryAux, OneNode.truncate, hi]
  · simp [OneNode.boundaryAux, hi]
end OneNode

namespace CoordNode

theorem infiniteOneCanonicalMap_firstDisagreement_meet
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {N M n : Nat} (u : OneNode N) (v : OneNode M)
    (hnN : n < N) (hnM : n < M)
    (hcut : u.truncate n = v.truncate n)
    (hdiff : u.boundaryAux n ≠ v.boundaryAux n) :
    meet
      (.one (f N) (infiniteOneCanonicalMap h₁ h₂ N u).val)
      (.one (f M) (infiniteOneCanonicalMap h₁ h₂ M v).val) =
      .one (f n)
        (infiniteOneCanonicalMap h₁ h₂ n (u.truncate n)).val := by
  let p : CoordNode :=
    .one (f n) (infiniteOneCanonicalMap h₁ h₂ n (u.truncate n)).val
  let a : CoordNode :=
    .one (f (n + 1))
      (infiniteOneCanonicalMap h₁ h₂ (n + 1) (u.truncate (n + 1))).val
  let b : CoordNode :=
    .one (f (n + 1))
      (infiniteOneCanonicalMap h₁ h₂ (n + 1) (v.truncate (n + 1))).val
  let x : CoordNode :=
    .one (f N) (infiniteOneCanonicalMap h₁ h₂ N u).val
  let y : CoordNode :=
    .one (f M) (infiniteOneCanonicalMap h₁ h₂ M v).val
  have hsrcA :
      (u.truncate n).succ (u.boundaryAux n) = u.truncate (n + 1) := by
    have h := (u.truncate (n + 1)).succ_truncate_boundary
    rw [u.truncate_truncate (Nat.le_succ n)] at h
    have hb : (u.truncate (n + 1)).boundaryAux n = u.boundaryAux n := by
      exact OneNode.boundaryAux_truncate_next _ _
    rw [hb] at h
    exact h
  have hsrcB :
      (u.truncate n).succ (v.boundaryAux n) = v.truncate (n + 1) := by
    rw [hcut]
    have h := (v.truncate (n + 1)).succ_truncate_boundary
    rw [v.truncate_truncate (Nat.le_succ n)] at h
    have hb : (v.truncate (n + 1)).boundaryAux n = v.boundaryAux n := by
      exact OneNode.boundaryAux_truncate_next _ _
    rw [hb] at h
    exact h
  have hlocal :=
    infiniteOneCanonicalMap_distinct_child_meet h₁ h₂ hf n
      (u.truncate n) (u.boundaryAux n) (v.boundaryAux n) hdiff
  rw [hsrcA, hsrcB] at hlocal
  have hpa : p ≤ a := by
    have htr := infiniteOneCanonicalMap_truncate h₁ h₂ hf
      n (n + 1) (by omega) (u.truncate (n + 1))
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.one (f n)
        ((infiniteOneCanonicalMap h₁ h₂ (n + 1)
          (u.truncate (n + 1))).val.truncate (f n)) = p
    rw [htr, u.truncate_truncate (Nat.le_succ n)]
  have hpb : p ≤ b := by
    have htr := infiniteOneCanonicalMap_truncate h₁ h₂ hf
      n (n + 1) (by omega) (v.truncate (n + 1))
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.one (f n)
        ((infiniteOneCanonicalMap h₁ h₂ (n + 1)
          (v.truncate (n + 1))).val.truncate (f n)) = p
    rw [htr, v.truncate_truncate (Nat.le_succ n), ← hcut]
  have hab : a ≠ b := by
    intro heq
    have hval :
        (infiniteOneCanonicalMap h₁ h₂ (n + 1)
          (u.truncate (n + 1))).val =
        (infiniteOneCanonicalMap h₁ h₂ (n + 1)
          (v.truncate (n + 1))).val := by
      injection heq
    have hsrc : u.truncate (n + 1) = v.truncate (n + 1) :=
      (infiniteOneCanonicalMap_injective h₁ h₂ hf (n + 1)) hval
    have hb := congrArg (fun z : OneNode (n + 1) => z.boundaryAux n) hsrc
    have hb' : u.boundaryAux n = v.boundaryAux n := by
      simpa only [OneNode.boundaryAux_truncate_next] using hb
    exact hdiff hb'
  have hax : a ≤ x := by
    have htr := infiniteOneCanonicalMap_truncate h₁ h₂ hf
      (n + 1) N (by omega) u
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.one (f (n + 1))
        ((infiniteOneCanonicalMap h₁ h₂ N u).val.truncate (f (n + 1))) = a
    rw [htr]
  have hby : b ≤ y := by
    have htr := infiniteOneCanonicalMap_truncate h₁ h₂ hf
      (n + 1) M (by omega) v
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.one (f (n + 1))
        ((infiniteOneCanonicalMap h₁ h₂ M v).val.truncate (f (n + 1))) = b
    rw [htr]
  have hdesc :=
    meet_descendants_distinct_parents a b x y rfl hab
      hax hby ⟨p, hpa, hpb⟩
  change meet x y = p
  exact hdesc.trans hlocal

end CoordNode
end ThreeUniformDiaries
