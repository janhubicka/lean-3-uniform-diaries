import ThreeUniformDiaries.CountableGenericEmbedding

/-!
# Track A: generic countable induced embedding extending an ACTUAL finite seed

The existing countable generic induction chooses an initial EMPTY finite
stage. For relative constructions it is useful to start from any already
chosen genuine `FiniteGenericStage G K n`. Iterating the SAME verified
one-step extension operation produces a countable induced embedding
whose first n images agree literally with the seed.

This is an ORDER-PRESERVING finite seed, not an arbitrary unordered
preembedding. It controls the induced 3-hypergraph relations and
nonedges, but NOT the TypeRespecting/role/oneMeet/twoMeet/future-reserve
conditions of full diaries. The remaining diary no-escape issue is
independent of this theorem.
-/

namespace ThreeUniformDiaries

namespace GenericEnumerated3Graph

/-- Extend one given actual ordered finite induced stage indefinitely.
No prior seed vertex is ever moved. -/
noncomputable def seededStages
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    {n : Nat} (s : FiniteGenericStage G K n) :
    (k : Nat) → FiniteGenericStage G K (n + k)
  | 0 => s
  | k + 1 => (seededStages G K s k).extend

/-- The seeded finite-stage chain literally fixes all old images. -/
theorem seededStages_succ_old
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    {n : Nat} (s : FiniteGenericStage G K n)
    (k : Nat) (i : Fin (n + k)) :
    ((G.seededStages K s (k + 1)).image (Fin.castSucc i)).val =
      ((G.seededStages K s k).image i).val := by
  exact FiniteGenericStage.extend_old (G.seededStages K s k) i

/-- All later seeded stages agree on each earlier source index. -/
theorem seededStages_stable
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    {n : Nat} (s : FiniteGenericStage G K n)
    (k l : Nat) (hkl : k ≤ l) (i : Fin (n + k)) :
    ((G.seededStages K s l).image ⟨i.val, by omega⟩).val =
      ((G.seededStages K s k).image i).val := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
      calc
        ((G.seededStages K s (l + 1)).image
          ⟨i.val, by omega⟩).val =
            ((G.seededStages K s l).image
              ⟨i.val, by omega⟩).val := by
                exact G.seededStages_succ_old K s l ⟨i.val, by omega⟩
        _ = ((G.seededStages K s k).image i).val := ih

/-- The infinite pointwise union of the seeded finite stages. -/
noncomputable def seededEmbedding
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    {n : Nat} (s : FiniteGenericStage G K n)
    (i : Nat) : Nat :=
  if hi : i < n then (s.image ⟨i, hi⟩).val
  else ((G.seededStages K s (i - n + 1)).image
    ⟨i, by omega⟩).val

/-- The seeded limit agrees with the specified stage at every
source coordinate already in the stage. -/
theorem seededEmbedding_at_stage
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    {n : Nat} (s : FiniteGenericStage G K n)
    (k i : Nat) (hi : i < n + k) :
    ((G.seededStages K s k).image ⟨i, hi⟩).val =
      G.seededEmbedding K s i := by
  by_cases hin : i < n
  · have h := G.seededStages_stable K s 0 k (Nat.zero_le k)
      (⟨i, by omega⟩ : Fin (n + 0))
    simpa [seededEmbedding, hin, seededStages] using h
  · let t := i - n + 1
    have ht : i < n + t := by dsimp [t]; omega
    have hle : t ≤ k := by dsimp [t]; omega
    have h := G.seededStages_stable K s t k hle
      (⟨i, ht⟩ : Fin (n + t))
    simpa [seededEmbedding, hin, t] using h

/-- Genericity extends any supplied ACTUAL finite ordered induced
embedding of a finite initial source segment. This is the
fully relative version of the ordinary generic embedding theorem;
it assumes no full diary structure and is NOT diary unavoidability. -/
theorem exists_countable_induced_embedding_extending_stage
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    {n : Nat} (s : FiniteGenericStage G K n) :
    ∃ f : Nat → Nat,
      StrictMono f ∧
      (∀ i : Fin n, f i.val = (s.image i).val) ∧
      (∀ a b c : Nat, a < b → b < c →
        (K.edge a b c ↔ G.graph.edge (f a) (f b) (f c))) := by
  refine ⟨G.seededEmbedding K s, ?_, ?_, ?_⟩
  · intro a b hab
    let T := G.seededStages K s (b + 1)
    have ha : a < n + (b + 1) := by omega
    have hb : b < n + (b + 1) := by omega
    have h : ((T.image ⟨a, ha⟩).val <
        (T.image ⟨b, hb⟩).val) :=
      T.mono (show (⟨a, ha⟩ : Fin (n + (b + 1))) <
        ⟨b, hb⟩ from hab)
    change ((G.seededStages K s (b + 1)).image ⟨a, ha⟩).val <
      ((G.seededStages K s (b + 1)).image ⟨b, hb⟩).val at h
    rw [G.seededEmbedding_at_stage K s (b + 1) a ha,
      G.seededEmbedding_at_stage K s (b + 1) b hb] at h
    exact h
  · intro i
    simp only [seededEmbedding, dif_pos i.isLt]
  · intro a b c hab hbc
    let T := G.seededStages K s (c + 1)
    have ha : a < n + (c + 1) := by omega
    have hb : b < n + (c + 1) := by omega
    have hc : c < n + (c + 1) := by omega
    have h := T.edge_iff
      (⟨a, ha⟩ : Fin (n + (c + 1)))
      (⟨b, hb⟩ : Fin (n + (c + 1)))
      (⟨c, hc⟩ : Fin (n + (c + 1))) hab hbc
    change K.edge a b c ↔
      G.graph.edge
        ((G.seededStages K s (c + 1)).image ⟨a, ha⟩).val
        ((G.seededStages K s (c + 1)).image ⟨b, hb⟩).val
        ((G.seededStages K s (c + 1)).image ⟨c, hc⟩).val at h
    rw [G.seededEmbedding_at_stage K s (c + 1) a ha,
      G.seededEmbedding_at_stage K s (c + 1) b hb,
      G.seededEmbedding_at_stage K s (c + 1) c hc] at h
    exact h

end GenericEnumerated3Graph
end ThreeUniformDiaries
