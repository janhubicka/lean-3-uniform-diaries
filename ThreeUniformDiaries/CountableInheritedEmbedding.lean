import ThreeUniformDiaries.FiniteInheritedStage

/-!
# A countable chain using the predecessor-relative gap condition

The source vertices are enumerated by natural numbers and each
non-initial vertex n+1 is assigned a prior source index parent n.
The concrete stage extension preserves all induced source hyperedges
while copying the bits on omitted target vertices below the
image of parent n.

This is the recursion required for Lemma Kiemb once the nodes of K_I
are supplied with a length-first enumeration and parent indices.
The theorem is deliberately parameterised by that schedule rather
than assuming K_I has already been enumerated.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

variable (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)

/-- One source vertex sent to the first target vertex. -/
def firstGenericStage : FiniteGenericStage G K 1 where
  bound := 1
  image := fun _ => ⟨0, by omega⟩
  mono := by
    intro i j hij
    have heq : i = j := Subsingleton.elim i j
    rw [heq] at hij
    exact (lt_irrefl j hij).elim
  edge_iff := by
    intro i j k hij _
    have heq : i = j := Subsingleton.elim i j
    rw [heq] at hij
    exact (lt_irrefl j hij).elim

/-- A chosen source parent for the vertex indexed n+1. -/
abbrev ParentSchedule := (n : Nat) → Fin (n + 1)

/-- Repeated inherited-gap extensions, with exactly n+1 source vertices
at stage n. -/
noncomputable def inheritedStages (parent : ParentSchedule) :
    (n : Nat) → FiniteGenericStage G K (n + 1)
  | 0 => firstGenericStage G K
  | n + 1 => (inheritedStages parent n).extendInherited (parent n)

/-- Successor stages leave all earlier source vertices fixed. -/
theorem inheritedStages_succ_old
    (parent : ParentSchedule) (n : Nat) (i : Fin (n + 1)) :
    ((G.inheritedStages K parent (n + 1)).image (Fin.castSucc i)).val =
      ((G.inheritedStages K parent n).image i).val := by
  exact FiniteGenericStage.extendInherited_old
    (G.inheritedStages K parent n) (parent n) i

/-- Coherence across arbitrary finite-stage extensions. -/
theorem inheritedStages_stable
    (parent : ParentSchedule) (n m : Nat) (hnm : n ≤ m)
    (i : Fin (n + 1)) :
    ((G.inheritedStages K parent m).image ⟨i.val, by omega⟩).val =
      ((G.inheritedStages K parent n).image i).val := by
  induction m, hnm using Nat.le_induction with
  | base =>
      rfl
  | succ m hm ih =>
      calc
        ((G.inheritedStages K parent (m + 1)).image
          ⟨i.val, by omega⟩).val =
            ((G.inheritedStages K parent m).image
              ⟨i.val, by omega⟩).val := by
                exact G.inheritedStages_succ_old K parent m
                  ⟨i.val, by omega⟩
        _ = ((G.inheritedStages K parent n).image i).val := ih

/-- The countable map is the union of the induced finite embeddings. -/
noncomputable def inheritedEmbedding
    (parent : ParentSchedule) (i : Nat) : Nat :=
  ((G.inheritedStages K parent i).image (Fin.last i)).val

theorem inheritedEmbedding_at_stage
    (parent : ParentSchedule) {i n : Nat} (hin : i ≤ n) :
    ((G.inheritedStages K parent n).image ⟨i, by omega⟩).val =
      G.inheritedEmbedding K parent i := by
  have h := G.inheritedStages_stable K parent i n hin (Fin.last i)
  simpa [inheritedEmbedding] using h

/-- For every schedule of earlier parents, inherited-gap recursion
produces an induced countable embedding. -/
theorem exists_countable_inherited_embedding
    (parent : ParentSchedule) :
    StrictMono (G.inheritedEmbedding K parent) ∧
      ∀ a b c : Nat, a < b → b < c →
        (K.edge a b c ↔
          G.graph.edge
            (G.inheritedEmbedding K parent a)
            (G.inheritedEmbedding K parent b)
            (G.inheritedEmbedding K parent c)) := by
  constructor
  · intro a b hab
    let S := G.inheritedStages K parent b
    have h := S.mono
      (show (⟨a, by omega⟩ : Fin (b + 1)) < Fin.last b from hab)
    change (S.image ⟨a, by omega⟩).val <
      (S.image (Fin.last b)).val at h
    simpa [inheritedEmbedding, S,
      G.inheritedEmbedding_at_stage K parent (show a ≤ b by omega)] using h
  · intro a b c hab hbc
    let S := G.inheritedStages K parent c
    have h := S.edge_iff
      ⟨a, by omega⟩ ⟨b, by omega⟩ (Fin.last c)
      (show a < b from hab) (show b < c from hbc)
    have ha : (S.image ⟨a, by omega⟩).val =
        G.inheritedEmbedding K parent a :=
      G.inheritedEmbedding_at_stage K parent (by omega)
    have hb : (S.image ⟨b, by omega⟩).val =
        G.inheritedEmbedding K parent b :=
      G.inheritedEmbedding_at_stage K parent (by omega)
    have hc : (S.image (Fin.last c)).val =
        G.inheritedEmbedding K parent c :=
      G.inheritedEmbedding_at_stage K parent (le_refl c)
    rw [ha, hb, hc] at h
    exact h


/-- The countable recursion satisfies the *exact* repaired (C2) rule
at each new source vertex: inherited below its selected parent image,
and zero for the other non-selected pairs. -/
theorem inheritedEmbedding_gap_step
    (parent : ParentSchedule) (n : Nat)
    (x y : Fin ((G.inheritedStages K parent n).bound))
    (hxy : x < y)
    (hgap :
      (¬ ∃ i : Fin (n + 1),
        (G.inheritedStages K parent n).image i = x) ∨
      (¬ ∃ j : Fin (n + 1),
        (G.inheritedStages K parent n).image j = y)) :
    (y < (G.inheritedStages K parent n).image (parent n) →
      (G.graph.edge x.val y.val
        (G.inheritedEmbedding K parent (n + 1)) ↔
       G.graph.edge x.val y.val
        (G.inheritedEmbedding K parent (parent n).val))) ∧
    ((G.inheritedStages K parent n).image (parent n) ≤ y →
      ¬ G.graph.edge x.val y.val
        (G.inheritedEmbedding K parent (n + 1))) := by
  let S := G.inheritedStages K parent n
  have hnew :
      G.inheritedEmbedding K parent (n + 1) =
        S.inheritedVertex (parent n) := by
    exact FiniteGenericStage.extendInherited_last S (parent n)
  have hpar :
      (S.image (parent n)).val =
        G.inheritedEmbedding K parent (parent n).val :=
    G.inheritedEmbedding_at_stage K parent (by omega)
  constructor
  · intro hy
    have h := (S.inheritedVertex_spec (parent n)).2.2.1
      x y hxy hgap hy
    rw [hnew, ← hpar]
    exact h
  · intro hy
    have h := (S.inheritedVertex_spec (parent n)).2.2.2
      x y hxy hgap hy
    rw [hnew]
    exact h

end GenericEnumerated3Graph
end ThreeUniformDiaries
