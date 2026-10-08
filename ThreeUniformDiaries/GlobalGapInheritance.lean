import ThreeUniformDiaries.CountableInheritedEmbedding

/-!
# Omitted-vertex consequences of the countable inherited-gap construction

The abstract propagation lemmas in InheritedGapExtension are deliberately
conditional.  Here we derive their concrete one-step hypotheses from the
constructed countable embedding itself.

An omitted target vertex is one outside the complete range of the
countable embedding, rather than merely outside a finite stage.  The
point of this module is to show that this stronger, invariant notion
satisfies the finite gap restrictions at *every* later stage.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

variable (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
variable (parent : ParentSchedule)

/-- A vertex outside the global image is absent from every finite stage. -/
theorem omitted_not_in_inherited_stage (n x : Nat)
    (hmiss : ∀ i : Nat, G.inheritedEmbedding K parent i ≠ x) :
    ¬ ∃ i : Fin (n + 1),
      ((G.inheritedStages K parent n).image i).val = x := by
  rintro ⟨i, hi⟩
  have hiStage :
      ((G.inheritedStages K parent n).image i).val =
        G.inheritedEmbedding K parent i.val := by
    simpa using (G.inheritedEmbedding_at_stage K parent
      (show i.val ≤ n by omega))
  exact hmiss i.val (hiStage.symm.trans hi)

/-- The parent image is below the bound of the finite stage. -/
theorem inherited_parent_below_bound (n : Nat) :
    G.inheritedEmbedding K parent (parent n).val <
      (G.inheritedStages K parent n).bound := by
  have h := ((G.inheritedStages K parent n).image (parent n)).isLt
  have hp := G.inheritedEmbedding_at_stage K parent
    (show (parent n).val ≤ n by omega)
  rw [hp] at h
  exact h

/-- On a pair containing a globally omitted vertex and lying below
the parent image, the new vertex copies the parent's edge bit. -/
theorem inherited_copy_omitted_pair (n x y : Nat)
    (hxy : x < y)
    (hy : y < G.inheritedEmbedding K parent (parent n).val)
    (hmiss : ∀ i : Nat, G.inheritedEmbedding K parent i ≠ x) :
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
    left
    rintro ⟨i, hi⟩
    have hval : (S.image i).val = x := congrArg Fin.val hi
    exact G.omitted_not_in_inherited_stage K parent n x hmiss ⟨i, hval⟩
  have hyp : yy < S.image (parent n) := by
    change y < (S.image (parent n)).val
    rw [hp]
    exact hy
  exact (G.inheritedEmbedding_gap_step K parent n xx yy hfin hgap).1 hyp

/-- A globally omitted vertex forms a non-edge with the parent and
the newly selected vertex: this is the other clause of repaired C2. -/
theorem inherited_zero_omitted_parent (n x : Nat)
    (hx : x < G.inheritedEmbedding K parent (parent n).val)
    (hmiss : ∀ i : Nat, G.inheritedEmbedding K parent i ≠ x) :
    ¬ G.graph.edge x
        (G.inheritedEmbedding K parent (parent n).val)
        (G.inheritedEmbedding K parent (n + 1)) := by
  let S := G.inheritedStages K parent n
  have hp : (S.image (parent n)).val =
      G.inheritedEmbedding K parent (parent n).val :=
    G.inheritedEmbedding_at_stage K parent (by omega)
  have hpb : (S.image (parent n)).val < S.bound :=
    (S.image (parent n)).isLt
  have hxb : x < S.bound := by omega
  let xx : Fin S.bound := ⟨x, hxb⟩
  let yy : Fin S.bound := S.image (parent n)
  have hfin : xx < yy := by
    change x < (S.image (parent n)).val
    rw [hp]
    exact hx
  have hgap :
      (¬ ∃ i : Fin (n + 1), S.image i = xx) ∨
      (¬ ∃ j : Fin (n + 1), S.image j = yy) := by
    left
    rintro ⟨i, hi⟩
    have hval : (S.image i).val = x := congrArg Fin.val hi
    exact G.omitted_not_in_inherited_stage K parent n x hmiss ⟨i, hval⟩
  have hyy : S.image (parent n) ≤ yy := le_refl _
  have hz := (G.inheritedEmbedding_gap_step K parent n xx yy hfin hgap).2 hyy
  simpa only [xx, yy, hp] using hz

end GenericEnumerated3Graph
end ThreeUniformDiaries
