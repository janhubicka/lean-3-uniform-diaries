import ThreeUniformDiaries.FixedPrefixGlobalGap
import ThreeUniformDiaries.InheritedGapExtension

/-!
# Propagate fixed-prefix inherited gaps along a parent branch

In the fixed initial segment, the target embedding is literally the
identity, so no target vertex below its image can be globally omitted.
Every subsequent branch successor follows the predecessor schedule,
which supplies the copy and zero conditions. The arguments below
make the split explicit and do not require a convex image.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

variable (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
variable (n0 : Nat) (hI : K.initialSegment n0 = G.graph.initialSegment n0)
variable (parent : PrefixParentSchedule n0)

/-- A branch follows each designated parent after leaving the fixed
initial segment. -/
def FollowsFixedParents (h : Nat → Nat) : Prop :=
  StrictMono h ∧
    ∀ t : Nat, n0 ≤ h (t + 1) →
      (parent (h (t + 1) - n0)).val = h t

/-- An omitted target pair copies its bits across one branch step.
For a step within the fixed prefix, omission is impossible. -/
theorem fixed_branch_copy (h : Nat → Nat)
    (hh : FollowsFixedParents n0 parent h)
    (t x y : Nat) (hxy : x < y)
    (hy : y < G.fixedInheritedEmbedding K n0 hI parent (h t))
    (hmiss :
      (∀ i : Nat, G.fixedInheritedEmbedding K n0 hI parent i ≠ x) ∨
      (∀ i : Nat, G.fixedInheritedEmbedding K n0 hI parent i ≠ y)) :
    G.graph.edge x y
      (G.fixedInheritedEmbedding K n0 hI parent (h (t + 1))) ↔
    G.graph.edge x y
      (G.fixedInheritedEmbedding K n0 hI parent (h t)) := by
  let f := G.fixedInheritedEmbedding K n0 hI parent
  by_cases hbefore : h (t + 1) < n0
  · have ht : h t < n0 :=
      (hh.1 (Nat.lt_succ_self t)).trans hbefore
    have hyN : y < n0 := by
      have hf := G.fixedInheritedEmbedding_prefix K n0 hI parent (h t) ht
      change y < f (h t) at hy
      rw [hf] at hy
      omega
    have hxN : x < n0 := by omega
    rcases hmiss with hx | hy'
    · exact False.elim (hx x
        (G.fixedInheritedEmbedding_prefix K n0 hI parent x hxN))
    · exact False.elim (hy' y
        (G.fixedInheritedEmbedding_prefix K n0 hI parent y hyN))
  · have hafter : n0 ≤ h (t + 1) := Nat.le_of_not_gt hbefore
    have hnew : n0 + (h (t + 1) - n0) = h (t + 1) := by omega
    have hp := hh.2 t hafter
    have hyp : y < f (parent (h (t + 1) - n0)).val := by
      simpa only [hp] using hy
    have hc := G.fixedInherited_copy_omitted_either K n0 hI parent
      (h (t + 1) - n0) x y hxy hyp hmiss
    simpa only [hnew, hp] using hc

/-- The first newly selected successor on a branch makes an omitted
target vertex into a nonedge with its branch parent. -/
theorem fixed_branch_new_zero (h : Nat → Nat)
    (hh : FollowsFixedParents n0 parent h)
    (t x : Nat)
    (hx : x < G.fixedInheritedEmbedding K n0 hI parent (h t))
    (hmiss : ∀ i : Nat,
      G.fixedInheritedEmbedding K n0 hI parent i ≠ x) :
    ¬ G.graph.edge x
      (G.fixedInheritedEmbedding K n0 hI parent (h t))
      (G.fixedInheritedEmbedding K n0 hI parent (h (t + 1))) := by
  let f := G.fixedInheritedEmbedding K n0 hI parent
  by_cases hbefore : h (t + 1) < n0
  · have ht : h t < n0 :=
      (hh.1 (Nat.lt_succ_self t)).trans hbefore
    have hxN : x < n0 := by
      have hf := G.fixedInheritedEmbedding_prefix K n0 hI parent (h t) ht
      change x < f (h t) at hx
      rw [hf] at hx
      omega
    exact False.elim (hmiss x
      (G.fixedInheritedEmbedding_prefix K n0 hI parent x hxN))
  · have hafter : n0 ≤ h (t + 1) := Nat.le_of_not_gt hbefore
    have hnew : n0 + (h (t + 1) - n0) = h (t + 1) := by omega
    have hp := hh.2 t hafter
    have hxp : x < f (parent (h (t + 1) - n0)).val := by
      simpa only [hp] using hx
    have hz := G.fixedInherited_zero_omitted_parent K n0 hI parent
      (h (t + 1) - n0) x hxp hmiss
    simpa only [hnew, hp] using hz

/-- Every omitted pair agrees on all subsequent branch vertices below
an earlier cut. -/
theorem fixed_branch_omitted_oneType (h : Nat → Nat)
    (hh : FollowsFixedParents n0 parent h)
    (w u v x y : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hxy : x < y)
    (hy : y < G.fixedInheritedEmbedding K n0 hI parent (h w))
    (hmiss :
      (∀ i : Nat, G.fixedInheritedEmbedding K n0 hI parent i ≠ x) ∨
      (∀ i : Nat, G.fixedInheritedEmbedding K n0 hI parent i ≠ y)) :
    G.graph.edge x y
      (G.fixedInheritedEmbedding K n0 hI parent (h u)) ↔
    G.graph.edge x y
      (G.fixedInheritedEmbedding K n0 hI parent (h v)) := by
  let e : Nat → Nat := fun t =>
    G.fixedInheritedEmbedding K n0 hI parent (h t)
  have he : Monotone e :=
    (((G.fixedInheritedEmbedding_isEmbedding K n0 hI parent).1).comp
      hh.1).monotone
  have hc :
      ∀ i a b : Nat, a < b → b < e i →
        ((∀ j, G.fixedInheritedEmbedding K n0 hI parent j ≠ a) ∨
         (∀ j, G.fixedInheritedEmbedding K n0 hI parent j ≠ b)) →
        (G.graph.edge a b (e (i + 1)) ↔
         G.graph.edge a b (e i)) := by
    intro i a b hab hbi hgap
    exact G.fixed_branch_copy K n0 hI parent h hh i a b hab hbi hgap
  exact G.graph.gap_oneTypes_constant e he
    (fun a => ∀ j, G.fixedInheritedEmbedding K n0 hI parent j ≠ a)
    hc w u v x y hwu hwv hxy hy hmiss

/-- An omitted target vertex produces no auxiliary test along any two
positions of a fixed-prefix canonical branch. -/
theorem fixed_branch_omitted_auxType (h : Nat → Nat)
    (hh : FollowsFixedParents n0 parent h)
    (u v x : Nat) (hu : u < v)
    (hx : x < G.fixedInheritedEmbedding K n0 hI parent (h u))
    (hmiss : ∀ i : Nat,
      G.fixedInheritedEmbedding K n0 hI parent i ≠ x) :
    ¬ G.graph.edge x
      (G.fixedInheritedEmbedding K n0 hI parent (h u))
      (G.fixedInheritedEmbedding K n0 hI parent (h v)) := by
  let e : Nat → Nat := fun t =>
    G.fixedInheritedEmbedding K n0 hI parent (h t)
  have he : StrictMono e :=
    ((G.fixedInheritedEmbedding_isEmbedding K n0 hI parent).1).comp hh.1
  have hc :
      ∀ i a b : Nat, a < b → b < e i →
        ((∀ j, G.fixedInheritedEmbedding K n0 hI parent j ≠ a) ∨
         (∀ j, G.fixedInheritedEmbedding K n0 hI parent j ≠ b)) →
        (G.graph.edge a b (e (i + 1)) ↔
         G.graph.edge a b (e i)) := by
    intro i a b hab hbi hgap
    exact G.fixed_branch_copy K n0 hI parent h hh i a b hab hbi hgap
  have hn :
      ∀ i a : Nat, a < e i →
        (∀ j, G.fixedInheritedEmbedding K n0 hI parent j ≠ a) →
          ¬ G.graph.edge a (e i) (e (i + 1)) := by
    intro i a hai ha
    exact G.fixed_branch_new_zero K n0 hI parent h hh i a hai ha
  exact G.graph.gap_auxTypes_zero e he
    (fun a => ∀ j, G.fixedInheritedEmbedding K n0 hI parent j ≠ a)
    hc hn u v x hu hx hmiss

end GenericEnumerated3Graph
end ThreeUniformDiaries
