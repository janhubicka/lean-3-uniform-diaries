import ThreeUniformDiaries.DiaryGenericExistenceByPairCode

/-!
# Track A geometry audit: relative fixed-anchor link extension in a generic 3-graph

The full finite extension property of an ACTUAL GenericEnumerated3Graph
is stronger than mere countable universality: a finite pattern around
one previously selected anchor vertex can be realized by a new vertex
arbitrarily far in the enumeration.

Fix anchor a and any finite set S of distinct vertices strictly after a.
The extension axiom prescribes edges on pairs (a,s), s in S, inside a
finite initial segment. It supplies a new t beyond any chosen threshold
with edges (a,s,t) for every s in S.

This is an honest *relative* one-step result in the ORIGINAL generic
3-hypergraph. It does not place t in an ARBITRARY induced universal
subcopy F[U], and does not realize the mixed marker/split conditions,
exact S1/S2 meets, or future order reserves of a full RoleDiary.
-/

namespace ThreeUniformDiaries

namespace GenericEnumerated3Graph

/-- For a finite collection of vertices above one fixed anchor a,
a generic 3-hypergraph has arbitrarily late common link neighbors.
The anchor a remains literally fixed, unlike independent finite copies. -/
theorem exists_arbitrarily_late_common_anchor_link_neighbor
    (G : GenericEnumerated3Graph)
    (a M : Nat) (S : Finset Nat)
    (hAbove : ∀ s : Nat, s ∈ S → a < s) :
    ∃ t : Nat, M < t ∧
      ∀ s : Nat, s ∈ S → G.graph.edge a s t := by
  classical
  let m : Nat := max (M + 1) (max (a + 1) ((S.sup id) + 1))
  have hmM : M < m := by
    have h : M + 1 ≤ m := le_max_left _ _
    omega
  have hmA : a < m := by
    have h : a + 1 ≤ m :=
      (le_max_left (a + 1) ((S.sup id) + 1)).trans
        (le_max_right (M + 1) (max (a + 1) ((S.sup id) + 1)))
    omega
  have hmS (s : Nat) (hs : s ∈ S) : s < m := by
    have hBound : s ≤ S.sup id :=
      Finset.le_sup (f := id) hs
    have h : (S.sup id) + 1 ≤ m :=
      (le_max_right (a + 1) ((S.sup id) + 1)).trans
        (le_max_right (M + 1) (max (a + 1) ((S.sup id) + 1)))
    omega
  let pattern : Fin m → Fin m → Bool := fun i j =>
    decide (i.val = a ∧ j.val ∈ S)
  obtain ⟨t, hmt, hPattern⟩ := G.extension m pattern
  refine ⟨t, by omega, ?_⟩
  intro s hs
  let i : Fin m := ⟨a, hmA⟩
  let j : Fin m := ⟨s, hmS s hs⟩
  have hij : i < j := by
    change a < s
    exact hAbove s hs
  have hBit : pattern i j = true := by
    simp [pattern, hs]
  exact (hPattern i j hij).mpr hBit

end GenericEnumerated3Graph

/-- Apply the relative fixed-root extension to the concrete pair-coded
generic hypergraph used by the diary formalization. -/
theorem canonical_generic_exists_late_common_anchor_link_neighbor
    (a M : Nat) (S : Finset Nat)
    (hAbove : ∀ s : Nat, s ∈ S → a < s) :
    ∃ t : Nat, M < t ∧
      ∀ s : Nat, s ∈ S →
        canonicalGenericEnumerated3Graph.graph.edge a s t :=
  canonicalGenericEnumerated3Graph.exists_arbitrarily_late_common_anchor_link_neighbor
    a M S hAbove

end ThreeUniformDiaries
