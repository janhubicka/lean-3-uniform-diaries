import ThreeUniformDiaries.CountableGenericEmbedding

/-!
# The inherited-gap extension as a coherent finite embedding stage

This builds on the concrete finite stages of CountableGenericEmbedding.
For a given earlier source vertex serving as immediate prefix parent, it
extends an induced finite stage while retaining every old image. Unlike
the ordinary generic extension, the new vertex also inherits the pair
bits involving unselected target vertices below the parent image.

The next step is to iterate this operation along the length-first
enumeration of K_I; the present theorem does not yet assert that global
enumeration or exact preservation of type meets.
-/

namespace ThreeUniformDiaries
namespace FiniteGenericStage

variable {G : GenericEnumerated3Graph}
  {K : Ordered3Graph Nat} {n : Nat}

/-- Choose the next vertex via the predecessor-relative generic rule. -/
noncomputable def inheritedVertex
    (s : FiniteGenericStage G K n) (parent : Fin n) : Nat :=
  Classical.choose
    (G.exists_extension_inheriting_gaps K n s.bound s.image
      s.mono (s.image parent))

/-- All three clauses of the inherited-gap finite extension. -/
theorem inheritedVertex_spec
    (s : FiniteGenericStage G K n) (parent : Fin n) :
    s.bound ≤ s.inheritedVertex parent ∧
    (∀ i j : Fin n, i < j →
      (K.edge i.val j.val n ↔
        G.graph.edge (s.image i).val (s.image j).val
          (s.inheritedVertex parent))) ∧
    (∀ x y : Fin s.bound, x < y →
      ((¬ ∃ i : Fin n, s.image i = x) ∨
       (¬ ∃ j : Fin n, s.image j = y)) →
      y < s.image parent →
      (G.graph.edge x.val y.val (s.inheritedVertex parent) ↔
        G.graph.edge x.val y.val (s.image parent).val)) ∧
    (∀ x y : Fin s.bound, x < y →
      ((¬ ∃ i : Fin n, s.image i = x) ∨
       (¬ ∃ j : Fin n, s.image j = y)) →
      s.image parent ≤ y →
      ¬ G.graph.edge x.val y.val (s.inheritedVertex parent)) :=
  Classical.choose_spec
    (G.exists_extension_inheriting_gaps K n s.bound s.image
      s.mono (s.image parent))

/-- The stronger rule gives another finite induced embedding, not merely
a predicate-realising point. -/
noncomputable def extendInherited
    (s : FiniteGenericStage G K n) (parent : Fin n) :
    FiniteGenericStage G K (n + 1) := by
  classical
  let v := s.inheritedVertex parent
  have hv : s.bound ≤ v := (s.inheritedVertex_spec parent).1
  let image' := appendImage s.image hv
  refine {
    bound := v + 1
    image := image'
    mono := appendImage_strictMono s.image hv s.mono
    edge_iff := ?_
  }
  intro i j k hij hjk
  have hi : i.val < n := by omega
  have hj : j.val < n := by omega
  by_cases hk : k.val < n
  · have hh :
        K.edge i.val j.val k.val ↔
          G.graph.edge
            (s.image ⟨i.val, hi⟩).val
            (s.image ⟨j.val, hj⟩).val
            (s.image ⟨k.val, hk⟩).val :=
      s.edge_iff ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk
    simpa [image', appendImage, hi, hj, hk] using hh
  · have hkval : k.val = n := by omega
    have hh :
        K.edge i.val j.val n ↔
          G.graph.edge
            (s.image ⟨i.val, hi⟩).val
            (s.image ⟨j.val, hj⟩).val v :=
      (s.inheritedVertex_spec parent).2.1
        ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
    simpa [image', appendImage, hi, hj, hk, hkval, v] using hh

/-- The stronger extension retains its source images on every old index. -/
theorem extendInherited_old
    (s : FiniteGenericStage G K n) (parent : Fin n) (i : Fin n) :
    ((s.extendInherited parent).image (Fin.castSucc i)).val =
      (s.image i).val := by
  simp [extendInherited, appendImage]

/-- The new source index is mapped to the inherited-gap witness. -/
theorem extendInherited_last
    (s : FiniteGenericStage G K n) (parent : Fin n) :
    ((s.extendInherited parent).image (Fin.last n)).val =
      s.inheritedVertex parent := by
  simp [extendInherited, appendImage]

end FiniteGenericStage
end ThreeUniformDiaries
