import ThreeUniformDiaries.FixedPrefixGapStep

/-!
# Global omitted-target gap transfer for a fixed initial source segment

A countable inherited embedding that begins by fixing a nonempty source
prefix satisfies the same predecessor-relative C2 rules as the
root-based version. Here we derive from the finite-stage C2 rule the
two statements about vertices outside the *eventual* image that will
be used to prove canonical-branch type preservation.

This module works with an arbitrary parent schedule and does not
assume the source K has already been identified with K_I.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

variable (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
variable (n0 : Nat) (hI : K.initialSegment n0 = G.graph.initialSegment n0)
variable (parent : PrefixParentSchedule n0)

/-- The selected parent is always below the current finite target bound. -/
theorem fixedInherited_parent_below_bound (t : Nat) :
    G.fixedInheritedEmbedding K n0 hI parent (parent t).val <
      (G.fixedInheritedStages K n0 hI parent t).bound := by
  let S := G.fixedInheritedStages K n0 hI parent t
  have h := (S.image (parent t)).isLt
  have hp := G.fixedInheritedEmbedding_at_stage K n0 hI parent
    t (parent t).val (parent t).isLt
  rw [hp] at h
  exact h

/-- Every pair below the parent image with at least one globally
omitted target endpoint copies its previous bit at the new image. -/
theorem fixedInherited_copy_omitted_either
    (t x y : Nat) (hxy : x < y)
    (hy : y < G.fixedInheritedEmbedding K n0 hI parent (parent t).val)
    (hmiss :
      (∀ i : Nat, G.fixedInheritedEmbedding K n0 hI parent i ≠ x) ∨
      (∀ i : Nat, G.fixedInheritedEmbedding K n0 hI parent i ≠ y)) :
    G.graph.edge x y
      (G.fixedInheritedEmbedding K n0 hI parent (n0 + t)) ↔
    G.graph.edge x y
      (G.fixedInheritedEmbedding K n0 hI parent (parent t).val) := by
  let S := G.fixedInheritedStages K n0 hI parent t
  have hp : (S.image (parent t)).val =
      G.fixedInheritedEmbedding K n0 hI parent (parent t).val :=
    G.fixedInheritedEmbedding_at_stage K n0 hI parent
      t (parent t).val (parent t).isLt
  have hyb : y < S.bound :=
    lt_trans hy (G.fixedInherited_parent_below_bound K n0 hI parent t)
  have hxb : x < S.bound := lt_trans hxy hyb
  let xx : Fin S.bound := ⟨x, hxb⟩
  let yy : Fin S.bound := ⟨y, hyb⟩
  have hfin : xx < yy := hxy
  have hgap :
      (¬ ∃ i : Fin (n0 + t), S.image i = xx) ∨
      (¬ ∃ j : Fin (n0 + t), S.image j = yy) := by
    rcases hmiss with hx | hy'
    · left
      rintro ⟨i, hi⟩
      have hval : (S.image i).val = x := congrArg Fin.val hi
      exact G.fixedInherited_omitted_stage K n0 hI parent t x hx ⟨i, hval⟩
    · right
      rintro ⟨j, hj⟩
      have hval : (S.image j).val = y := congrArg Fin.val hj
      exact G.fixedInherited_omitted_stage K n0 hI parent t y hy' ⟨j, hval⟩
  have hyp : yy < S.image (parent t) := by
    change y < (S.image (parent t)).val
    rw [hp]
    exact hy
  exact (G.fixedInherited_gap_step K n0 hI parent
    t xx yy hfin hgap).1 hyp

/-- A globally omitted vertex contributes no edge through an inherited
step's selected parent and its newly created target vertex. -/
theorem fixedInherited_zero_omitted_parent
    (t x : Nat)
    (hx : x < G.fixedInheritedEmbedding K n0 hI parent (parent t).val)
    (hmiss : ∀ i : Nat,
      G.fixedInheritedEmbedding K n0 hI parent i ≠ x) :
    ¬ G.graph.edge x
        (G.fixedInheritedEmbedding K n0 hI parent (parent t).val)
        (G.fixedInheritedEmbedding K n0 hI parent (n0 + t)) := by
  let S := G.fixedInheritedStages K n0 hI parent t
  have hp : (S.image (parent t)).val =
      G.fixedInheritedEmbedding K n0 hI parent (parent t).val :=
    G.fixedInheritedEmbedding_at_stage K n0 hI parent
      t (parent t).val (parent t).isLt
  have hxb : x < S.bound := by
    exact lt_trans hx (G.fixedInherited_parent_below_bound K n0 hI parent t)
  let xx : Fin S.bound := ⟨x, hxb⟩
  let yy : Fin S.bound := S.image (parent t)
  have hfin : xx < yy := by
    change x < (S.image (parent t)).val
    rw [hp]
    exact hx
  have hgap :
      (¬ ∃ i : Fin (n0 + t), S.image i = xx) ∨
      (¬ ∃ j : Fin (n0 + t), S.image j = yy) := by
    left
    rintro ⟨i, hi⟩
    have hval : (S.image i).val = x := congrArg Fin.val hi
    exact G.fixedInherited_omitted_stage K n0 hI parent t x hmiss ⟨i, hval⟩
  have hy : S.image (parent t) ≤ yy := le_refl _
  have hz := (G.fixedInherited_gap_step K n0 hI parent
    t xx yy hfin hgap).2 hy
  simpa only [xx, yy, hp] using hz

end GenericEnumerated3Graph
end ThreeUniformDiaries
