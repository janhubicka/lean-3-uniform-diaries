import ThreeUniformDiaries.GlobalGapInheritance

/-!
# Concrete inherited-gap propagation along a branch

A branch is specified by a strictly increasing sequence h : Nat -> Nat
of source indices such that, for every t, the chosen parent of the
node indexed h(t+1) is precisely h(t). The countable inherited-gap
construction already provides the copy/zero rules for each source
vertex and its designated parent. These rules imply the exact
gap-vertex comparisons required when proving type and auxiliary-type
meet preservation for a branch of K_I.

This file does not assume that the source graph is K_I. Its parent-path
condition will follow from the explicit size-first K_I enumeration.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

variable (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
variable (parent : ParentSchedule)

private def missed (x : Nat) : Prop :=
  ∀ i : Nat, G.inheritedEmbedding K parent i ≠ x

/-- Copying works whenever either endpoint of the old pair is outside
the whole target image, not just when its smaller endpoint is. -/
theorem inherited_copy_omitted_either (n x y : Nat)
    (hxy : x < y)
    (hy : y < G.inheritedEmbedding K parent (parent n).val)
    (hmiss : missed G K parent x ∨ missed G K parent y) :
    G.graph.edge x y (G.inheritedEmbedding K parent (n + 1)) ↔
      G.graph.edge x y
        (G.inheritedEmbedding K parent (parent n).val) := by
  let S := G.inheritedStages K parent n
  have hp : (S.image (parent n)).val =
      G.inheritedEmbedding K parent (parent n).val :=
    G.inheritedEmbedding_at_stage K parent (by omega)
  have hyb : y < S.bound :=
    lt_trans hy (G.inherited_parent_below_bound K parent n)
  have hxb : x < S.bound := lt_trans hxy hyb
  let xx : Fin S.bound := ⟨x, hxb⟩
  let yy : Fin S.bound := ⟨y, hyb⟩
  have hfin : xx < yy := hxy
  have hgap :
      (¬ ∃ i : Fin (n + 1), S.image i = xx) ∨
      (¬ ∃ j : Fin (n + 1), S.image j = yy) := by
    rcases hmiss with hx | hy'
    · left
      rintro ⟨i, hi⟩
      have hval : (S.image i).val = x := congrArg Fin.val hi
      exact G.omitted_not_in_inherited_stage K parent n x hx ⟨i, hval⟩
    · right
      rintro ⟨i, hi⟩
      have hval : (S.image i).val = y := congrArg Fin.val hi
      exact G.omitted_not_in_inherited_stage K parent n y hy' ⟨i, hval⟩
  have hyp : yy < S.image (parent n) := by
    change y < (S.image (parent n)).val
    rw [hp]
    exact hy
  exact (G.inheritedEmbedding_gap_step K parent n xx yy hfin hgap).1 hyp

/-- A branch in the source indexing which follows the selected parent
at every successor. -/
def FollowsParents (h : Nat → Nat) : Prop :=
  StrictMono h ∧
    ∀ t : Nat, (parent (h (t + 1) - 1)).val = h t

/-- Concrete copying across successive vertices of a parent branch. -/
theorem inherited_branch_copy (h : Nat → Nat)
    (hh : FollowsParents parent h)
    (t x y : Nat) (hxy : x < y)
    (hy : y < G.inheritedEmbedding K parent (h t))
    (hmiss : missed G K parent x ∨ missed G K parent y) :
    G.graph.edge x y (G.inheritedEmbedding K parent (h (t + 1))) ↔
      G.graph.edge x y (G.inheritedEmbedding K parent (h t)) := by
  have hlt : h t < h (t + 1) :=
    hh.1 (Nat.lt_succ_self t)
  have heq : (h (t + 1) - 1) + 1 = h (t + 1) := by omega
  have hpar : (parent (h (t + 1) - 1)).val = h t := hh.2 t
  have hy' :
      y < G.inheritedEmbedding K parent
        (parent (h (t + 1) - 1)).val := by
    simpa [hpar] using hy
  have hc := G.inherited_copy_omitted_either K parent
    (h (t + 1) - 1) x y hxy hy' hmiss
  simpa only [heq, hpar] using hc

/-- Concrete zero test with the branch predecessor and its next vertex. -/
theorem inherited_branch_new_zero (h : Nat → Nat)
    (hh : FollowsParents parent h)
    (t x : Nat)
    (hx : x < G.inheritedEmbedding K parent (h t))
    (hmiss : missed G K parent x) :
    ¬ G.graph.edge x
      (G.inheritedEmbedding K parent (h t))
      (G.inheritedEmbedding K parent (h (t + 1))) := by
  have hlt : h t < h (t + 1) :=
    hh.1 (Nat.lt_succ_self t)
  have heq : (h (t + 1) - 1) + 1 = h (t + 1) := by omega
  have hpar : (parent (h (t + 1) - 1)).val = h t := hh.2 t
  have hx' :
      x < G.inheritedEmbedding K parent
        (parent (h (t + 1) - 1)).val := by
    simpa [hpar] using hx
  have hz := G.inherited_zero_omitted_parent K parent
    (h (t + 1) - 1) x hx' hmiss
  simpa only [heq, hpar] using hz

/-- All omitted-pair edge bits are constant along a branch below the
image of its earlier cut vertex. -/
theorem inherited_branch_omitted_oneType
    (h : Nat → Nat) (hh : FollowsParents parent h)
    (w u v x y : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hxy : x < y)
    (hyw : y < G.inheritedEmbedding K parent (h w))
    (hmiss : missed G K parent x ∨ missed G K parent y) :
    G.graph.edge x y (G.inheritedEmbedding K parent (h u)) ↔
      G.graph.edge x y (G.inheritedEmbedding K parent (h v)) := by
  let e : Nat → Nat := fun t => G.inheritedEmbedding K parent (h t)
  have he : Monotone e := by
    have hs : StrictMono e :=
      ((G.exists_countable_inherited_embedding K parent).1).comp hh.1
    exact hs.monotone
  have hcopy :
      ∀ i x y : Nat, x < y → y < e i →
        (missed G K parent x ∨ missed G K parent y) →
          (G.graph.edge x y (e (i + 1)) ↔
           G.graph.edge x y (e i)) := by
    intro i a b hab hbi hgap
    exact G.inherited_branch_copy K parent h hh i a b hab hbi hgap
  exact G.graph.gap_oneTypes_constant e he (missed G K parent)
    hcopy w u v x y hwu hwv hxy hyw hmiss

/-- Every auxiliary test involving a target vertex omitted from the
global image is a non-edge along a source branch. -/
theorem inherited_branch_omitted_auxType
    (h : Nat → Nat) (hh : FollowsParents parent h)
    (u v x : Nat) (huv : u < v)
    (hx : x < G.inheritedEmbedding K parent (h u))
    (hmiss : missed G K parent x) :
    ¬ G.graph.edge x
      (G.inheritedEmbedding K parent (h u))
      (G.inheritedEmbedding K parent (h v)) := by
  let e : Nat → Nat := fun t => G.inheritedEmbedding K parent (h t)
  have he : StrictMono e :=
    ((G.exists_countable_inherited_embedding K parent).1).comp hh.1
  have hcopy :
      ∀ i x y : Nat, x < y → y < e i →
        (missed G K parent x ∨ missed G K parent y) →
          (G.graph.edge x y (e (i + 1)) ↔
           G.graph.edge x y (e i)) := by
    intro i a b hab hbi hgap
    exact G.inherited_branch_copy K parent h hh i a b hab hbi hgap
  have hnew :
      ∀ i x : Nat, x < e i → missed G K parent x →
        ¬ G.graph.edge x (e i) (e (i + 1)) := by
    intro i a hai hmiss
    exact G.inherited_branch_new_zero K parent h hh i a hai hmiss
  exact G.graph.gap_auxTypes_zero e he (missed G K parent)
    hcopy hnew u v x huv hx hmiss

end GenericEnumerated3Graph
end ThreeUniformDiaries
