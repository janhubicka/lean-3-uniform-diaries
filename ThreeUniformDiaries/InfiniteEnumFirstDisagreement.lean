import ThreeUniformDiaries.InfiniteOneEnumDistinctMeets
import ThreeUniformDiaries.DistinctParentDescendantMeets
import ThreeUniformDiaries.InfiniteCanonicalAuxOneRestriction
import ThreeUniformDiaries.InfiniteCanonicalInjectivity

/-!
# First-disagreement meet preservation for arbitrary enumeration-type nodes

The genuine infinite enumeration canonical map is known to send
DIFFERENT IMMEDIATE SOURCE CHILDREN into separate ambient
successor cones. We extend this fact from immediate children to
two nodes at possibly different source levels N and M that first
disagree at an index n below both levels.

The map of both full source nodes then meets exactly at the
canonical enumeration image of their common prefix at level n. This is the
essential non-consecutive-level case in the geometric meet-closure
step of the manuscript's canonical composition lemma.
-/

namespace ThreeUniformDiaries

namespace EnumNode
/-- Boundary singleton parameter is unaffected by truncating
the enumeration node just after the boundary index. -/
theorem boundaryAux_truncate_next {N : Nat} (a : EnumNode N) (n : Nat) :
    (a.truncate (n + 1)).boundaryOne n = a.boundaryOne n := by
  apply OneNode.ext_pairs
  funext i j
  by_cases hi : i < j ∧ j < n
  · simp [EnumNode.boundaryOne, EnumNode.truncate, hi]
  · simp [EnumNode.boundaryOne, hi]
end EnumNode

namespace CoordNode

theorem infiniteEnumCanonicalMap_firstDisagreement_meet
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    {N M n : Nat} (u : EnumNode N) (v : EnumNode M)
    (hnN : n < N) (hnM : n < M)
    (hcut : u.truncate n = v.truncate n)
    (hdiff : u.boundaryOne n ≠ v.boundaryOne n) :
    meet
      (.enum (f N) (infiniteEnumCanonicalMap h₀ h₁ h₂ N u).val)
      (.enum (f M) (infiniteEnumCanonicalMap h₀ h₁ h₂ M v).val) =
      .enum (f n)
        (infiniteEnumCanonicalMap h₀ h₁ h₂ n (u.truncate n)).val := by
  let p : CoordNode :=
    .enum (f n) (infiniteEnumCanonicalMap h₀ h₁ h₂ n (u.truncate n)).val
  let a : CoordNode :=
    .enum (f (n + 1))
      (infiniteEnumCanonicalMap h₀ h₁ h₂ (n + 1) (u.truncate (n + 1))).val
  let b : CoordNode :=
    .enum (f (n + 1))
      (infiniteEnumCanonicalMap h₀ h₁ h₂ (n + 1) (v.truncate (n + 1))).val
  let x : CoordNode :=
    .enum (f N) (infiniteEnumCanonicalMap h₀ h₁ h₂ N u).val
  let y : CoordNode :=
    .enum (f M) (infiniteEnumCanonicalMap h₀ h₁ h₂ M v).val
  have hsrcA :
      (u.truncate n).succ (u.boundaryOne n) = u.truncate (n + 1) := by
    have h := (u.truncate (n + 1)).succ_truncate_boundary
    rw [u.truncate_truncate (Nat.le_succ n)] at h
    have hb : (u.truncate (n + 1)).boundaryOne n = u.boundaryOne n := by
      exact EnumNode.boundaryOne_truncate_next _ _
    rw [hb] at h
    exact h
  have hsrcB :
      (u.truncate n).succ (v.boundaryOne n) = v.truncate (n + 1) := by
    rw [hcut]
    have h := (v.truncate (n + 1)).succ_truncate_boundary
    rw [v.truncate_truncate (Nat.le_succ n)] at h
    have hb : (v.truncate (n + 1)).boundaryOne n = v.boundaryOne n := by
      exact EnumNode.boundaryOne_truncate_next _ _
    rw [hb] at h
    exact h
  have hlocal :=
    infiniteEnumCanonicalMap_distinct_child_meet h₀ h₁ h₂ hf n
      (u.truncate n) (u.boundaryOne n) (v.boundaryOne n) hdiff
  rw [hsrcA, hsrcB] at hlocal
  have hpa : p ≤ a := by
    have htr := infiniteEnumCanonicalMap_truncate h₀ h₁ h₂ hf
      n (n + 1) (by omega) (u.truncate (n + 1))
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.enum (f n)
        ((infiniteEnumCanonicalMap h₀ h₁ h₂ (n + 1)
          (u.truncate (n + 1))).val.truncate (f n)) = p
    rw [htr, u.truncate_truncate (Nat.le_succ n)]
  have hpb : p ≤ b := by
    have htr := infiniteEnumCanonicalMap_truncate h₀ h₁ h₂ hf
      n (n + 1) (by omega) (v.truncate (n + 1))
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.enum (f n)
        ((infiniteEnumCanonicalMap h₀ h₁ h₂ (n + 1)
          (v.truncate (n + 1))).val.truncate (f n)) = p
    rw [htr, v.truncate_truncate (Nat.le_succ n), ← hcut]
  have hab : a ≠ b := by
    intro heq
    have hval :
        (infiniteEnumCanonicalMap h₀ h₁ h₂ (n + 1)
          (u.truncate (n + 1))).val =
        (infiniteEnumCanonicalMap h₀ h₁ h₂ (n + 1)
          (v.truncate (n + 1))).val := by
      injection heq
    have hsrc : u.truncate (n + 1) = v.truncate (n + 1) :=
      (infiniteEnumCanonicalMap_injective h₀ h₁ h₂ hf (n + 1)) hval
    have hb := congrArg (fun z : EnumNode (n + 1) => z.boundaryOne n) hsrc
    have hb' : u.boundaryOne n = v.boundaryOne n := by
      simpa only [EnumNode.boundaryOne_truncate_next] using hb
    exact hdiff hb'
  have hax : a ≤ x := by
    have htr := infiniteEnumCanonicalMap_truncate h₀ h₁ h₂ hf
      (n + 1) N (by omega) u
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.enum (f (n + 1))
        ((infiniteEnumCanonicalMap h₀ h₁ h₂ N u).val.truncate (f (n + 1))) = a
    rw [htr]
  have hby : b ≤ y := by
    have htr := infiniteEnumCanonicalMap_truncate h₀ h₁ h₂ hf
      (n + 1) M (by omega) v
    refine ⟨hf.monotone (by omega), ?_⟩
    change
      CoordNode.enum (f (n + 1))
        ((infiniteEnumCanonicalMap h₀ h₁ h₂ M v).val.truncate (f (n + 1))) = b
    rw [htr]
  have hdesc :=
    meet_descendants_distinct_parents a b x y rfl hab
      hax hby ⟨p, hpa, hpb⟩
  change meet x y = p
  exact hdesc.trans hlocal

end CoordNode
end ThreeUniformDiaries
