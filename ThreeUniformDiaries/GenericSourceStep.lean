import ThreeUniformDiaries.GenericExtensionStep

/-!
# Generic extension using the next source vertex

The local C1/C2 lemma from `GenericExtensionStep` is now specialized to
the actual source hypergraph: a finite strictly increasing tuple of already
chosen ambient vertices determines the prescribed edge pattern for the next
source vertex.

The next edge pattern is defined by existence of a preimage pair. Strict
monotonicity makes the preimage unique, so its value is exactly the desired
source edge. This is the finite combinatorial step used in `lem:Kiemb`,
before the countable recursive construction.
-/

namespace ThreeUniformDiaries

namespace GenericEnumerated3Graph

/-- For a source hypergraph K, a strictly increasing finite tuple of
previously embedded vertices admits a new vertex realising exactly the
source triples through the next vertex; all other old pairs are non-edges. -/
theorem exists_extension_for_source
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (n m : Nat)
    (old : Fin n → Fin m)
    (hmono : StrictMono old) :
    ∃ v : Nat, m ≤ v ∧
      (∀ i j : Fin n, i < j →
        (K.edge i.val j.val n ↔
          G.graph.edge (old i).val (old j).val v)) ∧
      (∀ x y : Fin m, x < y →
        ((¬ ∃ i : Fin n, old i = x) ∨
         (¬ ∃ j : Fin n, old j = y)) →
        ¬ G.graph.edge x.val y.val v) := by
  classical
  let pattern : Fin m → Fin m → Bool :=
    fun x y => decide (∃ i j : Fin n,
      i < j ∧ old i = x ∧ old j = y ∧ K.edge i.val j.val n)
  obtain ⟨v, hv, hpat⟩ := G.extension m pattern
  have hp (i j : Fin n) (hij : i < j) :
      pattern (old i) (old j) = true ↔ K.edge i.val j.val n := by
    change
      decide (∃ i' j' : Fin n,
        i' < j' ∧ old i' = old i ∧ old j' = old j ∧
          K.edge i'.val j'.val n) = true ↔ K.edge i.val j.val n
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i', j', _, hi, hj, hEdge⟩
      have hieq : i' = i := hmono.injective hi
      have hjeq : j' = j := hmono.injective hj
      subst i'
      subst j'
      exact hEdge
    · intro hEdge
      exact ⟨i, j, hij, rfl, rfl, hEdge⟩
  refine ⟨v, hv, ?_, ?_⟩
  · intro i j hij
    exact (hp i j hij).symm.trans
      ((hpat (old i) (old j) (hmono hij)).symm)
  · intro x y hxy houtside hEdge
    have hprescribed : pattern x y = true :=
      (hpat x y hxy).mp hEdge
    have hsource : ∃ i j : Fin n,
        i < j ∧ old i = x ∧ old j = y ∧
        K.edge i.val j.val n := by
      simpa only [pattern, decide_eq_true_eq] using hprescribed
    rcases hsource with ⟨i, j, _, hi, hj, _⟩
    rcases houtside with hnotx | hnoty
    · exact hnotx ⟨i, hi⟩
    · exact hnoty ⟨j, hj⟩

end GenericEnumerated3Graph

end ThreeUniformDiaries
