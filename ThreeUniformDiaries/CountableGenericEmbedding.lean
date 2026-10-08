import ThreeUniformDiaries.InheritedGapExtension

/-!
# Coherent finite stages and a countable generic hypergraph embedding

The old and the strengthened local extension lemmas operate on a finite
initial segment.  This file constructs an increasing chain of finite
embeddings, retaining all already chosen images, and then defines an
induced embedding from an arbitrary enumerated hypergraph into the
enumerated generic hypergraph.

The argument uses the unstrengthened source extension. The remaining
K_I task is to run the same recursion with the predecessor-relative
gap prescription, whose finite consistency was checked separately.
-/

namespace ThreeUniformDiaries

/-- Extend a finite increasing image tuple by a new point at or above its
current target bound. -/
def appendImage {n m v : Nat} (old : Fin n → Fin m)
    (hmv : m ≤ v) (i : Fin (n + 1)) : Fin (v + 1) :=
  if h : i.val < n then
    ⟨(old ⟨i.val, h⟩).val, by
      have hb := (old ⟨i.val, h⟩).isLt
      omega⟩
  else
    ⟨v, by omega⟩

@[simp] theorem appendImage_old {n m v : Nat}
    (old : Fin n → Fin m) (hmv : m ≤ v) (i : Fin n) :
    (appendImage old hmv (Fin.castSucc i)).val = (old i).val := by
  simp [appendImage, i.isLt]

@[simp] theorem appendImage_last {n m v : Nat}
    (old : Fin n → Fin m) (hmv : m ≤ v) :
    (appendImage old hmv (Fin.last n)).val = v := by
  simp [appendImage]

theorem appendImage_strictMono {n m v : Nat}
    (old : Fin n → Fin m) (hmv : m ≤ v) (hmono : StrictMono old) :
    StrictMono (appendImage old hmv) := by
  intro i j hij
  have hi : i.val < n := by omega
  by_cases hj : j.val < n
  · have hh : (⟨i.val, hi⟩ : Fin n) < ⟨j.val, hj⟩ := hij
    have hout := hmono hh
    change (old ⟨i.val, hi⟩).val < (old ⟨j.val, hj⟩).val at hout
    change (appendImage old hmv i).val < (appendImage old hmv j).val
    simpa [appendImage, hi, hj] using hout
  · have hbound : (old ⟨i.val, hi⟩).val < v :=
      lt_of_lt_of_le (old ⟨i.val, hi⟩).isLt hmv
    change (appendImage old hmv i).val < (appendImage old hmv j).val
    simpa [appendImage, hi, hj] using hbound

/-- A finite induced copy of the first n vertices of a source hypergraph. -/
structure FiniteGenericStage
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat) (n : Nat) where
  bound : Nat
  image : Fin n → Fin bound
  mono : StrictMono image
  edge_iff : ∀ i j k : Fin n, i < j → j < k →
    (K.edge i.val j.val k.val ↔
      G.graph.edge (image i).val (image j).val (image k).val)

namespace FiniteGenericStage

variable (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)

/-- The unique empty stage. -/
def empty : FiniteGenericStage G K 0 where
  bound := 0
  image := fun i => Fin.elim0 i
  mono := by
    intro i j _
    exact Fin.elim0 i
  edge_iff := by
    intro i j k _ _
    exact Fin.elim0 i

variable {G K} {n : Nat}

/-- Genericity produces a new point after the stage bound. -/
noncomputable def newVertex (s : FiniteGenericStage G K n) : Nat :=
  Classical.choose
    (G.exists_extension_for_source K n s.bound s.image s.mono)

theorem newVertex_spec (s : FiniteGenericStage G K n) :
    s.bound ≤ s.newVertex ∧
      ∀ i j : Fin n, i < j →
        (K.edge i.val j.val n ↔
          G.graph.edge (s.image i).val (s.image j).val s.newVertex) :=
  (Classical.choose_spec
    (G.exists_extension_for_source K n s.bound s.image s.mono)).1.1,
  (Classical.choose_spec
    (G.exists_extension_for_source K n s.bound s.image s.mono)).2.1

/-- Adjoin the next source vertex without moving earlier images. -/
noncomputable def extend (s : FiniteGenericStage G K n) :
    FiniteGenericStage G K (n + 1) := by
  classical
  let v := s.newVertex
  have hv : s.bound ≤ v := (s.newVertex_spec).1
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
      (s.newVertex_spec).2 ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
    simpa [image', appendImage, hi, hj, hk, hkval, v] using hh

/-- Earlier images are unchanged after a successor stage. -/
theorem extend_old (s : FiniteGenericStage G K n) (i : Fin n) :
    (s.extend.image (Fin.castSucc i)).val = (s.image i).val := by
  simp [extend, appendImage]

/-- The last vertex of the successor stage is the new chosen point. -/
theorem extend_last (s : FiniteGenericStage G K n) :
    (s.extend.image (Fin.last n)).val = s.newVertex := by
  simp [extend, appendImage]

end FiniteGenericStage

namespace GenericEnumerated3Graph

/-- The recursively defined chain of finite induced embeddings. -/
noncomputable def finiteStages (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat) :
    (n : Nat) → FiniteGenericStage G K n
  | 0 => FiniteGenericStage.empty G K
  | n + 1 => (finiteStages G K n).extend

/-- Consecutive stages have exactly the same old vertex images. -/
theorem finiteStages_succ_old (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat) (n : Nat) (i : Fin n) :
    ((G.finiteStages K (n + 1)).image (Fin.castSucc i)).val =
      ((G.finiteStages K n).image i).val := by
  exact FiniteGenericStage.extend_old (G.finiteStages K n) i

/-- Every finite stage agrees with all later stages on its indices. -/
theorem finiteStages_stable (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat) (n m : Nat) (hnm : n ≤ m)
    (i : Fin n) :
    ((G.finiteStages K m).image ⟨i.val, by omega⟩).val =
      ((G.finiteStages K n).image i).val := by
  induction m, hnm using Nat.le_induction with
  | base =>
      rfl
  | succ m hm ih =>
      calc
        ((G.finiteStages K (m + 1)).image ⟨i.val, by omega⟩).val =
            ((G.finiteStages K m).image ⟨i.val, by omega⟩).val := by
          exact G.finiteStages_succ_old K m ⟨i.val, by omega⟩
        _ = ((G.finiteStages K n).image i).val := ih

/-- The countable map is the union of the coherent finite images. -/
noncomputable def countableEmbedding
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (i : Nat) : Nat :=
  ((G.finiteStages K (i + 1)).image (Fin.last i)).val

theorem countableEmbedding_at_stage
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    {i n : Nat} (hin : i < n) :
    ((G.finiteStages K n).image ⟨i, hin⟩).val =
      G.countableEmbedding K i := by
  have hi := G.finiteStages_stable K (i + 1) n (by omega)
    (Fin.last i)
  simpa [countableEmbedding] using hi

/-- Genericity yields a strictly increasing countable induced embedding. -/
theorem exists_countable_induced_embedding
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat) :
    ∃ f : Nat → Nat, StrictMono f ∧
      ∀ a b c : Nat, a < b → b < c →
        (K.edge a b c ↔ G.graph.edge (f a) (f b) (f c)) := by
  refine ⟨G.countableEmbedding K, ?_, ?_⟩
  · intro a b hab
    let S := G.finiteStages K (b + 1)
    have h := S.mono
      (show (⟨a, by omega⟩ : Fin (b + 1)) < Fin.last b from hab)
    change (S.image ⟨a, by omega⟩).val <
      (S.image (Fin.last b)).val at h
    simpa [countableEmbedding, S,
      G.countableEmbedding_at_stage K (show a < b + 1 by omega)] using h
  · intro a b c hab hbc
    let S := G.finiteStages K (c + 1)
    have h := S.edge_iff
      ⟨a, by omega⟩ ⟨b, by omega⟩ (Fin.last c)
      (show a < b from hab) (show b < c from hbc)
    simpa only [countableEmbedding_at_stage, Fin.val_last] using h

end GenericEnumerated3Graph
end ThreeUniformDiaries
