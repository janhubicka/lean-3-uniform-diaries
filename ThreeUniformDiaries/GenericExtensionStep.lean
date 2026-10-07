import ThreeUniformDiaries.AuxTypes
import Mathlib.Data.Finset.Basic

/-!
# One-step generic extension for the branch hypergraph embedding

This is the finite extension step used in Lemma `lem:Kiemb` of the
3-uniform diaries manuscript.  Fix the images `R` of the already embedded
vertices in an initial segment `m`, and a prescribed edge pattern
`inside` on pairs from `R`.  Genericity realizes that pattern while
setting every pair with an endpoint outside `R` to a non-edge.

This proves compatibility of manuscript conditions (C1) and (C2) and their
simultaneous realization.  It does **not** yet construct the infinite
embedding `K_I → G` or verify preservation of auxiliary meets.
-/

namespace ThreeUniformDiaries

/-- Extension property of a generic enumerated 3-uniform hypergraph.

Every Boolean pattern on pairs of a finite initial segment is realized
by some new vertex beyond that segment. -/
structure GenericEnumerated3Graph where
  graph : Ordered3Graph Nat
  extension :
    ∀ (m : Nat) (pattern : Fin m → Fin m → Bool),
      ∃ v : Nat, m ≤ v ∧
        ∀ i j : Fin m, i < j →
          (graph.edge i.val j.val v ↔ pattern i j = true)

namespace GenericEnumerated3Graph

/-- The pattern required by (C1) and (C2): prescribed edges between
previously embedded vertices, and no edges through other old vertices. -/
noncomputable def extendPattern (m : Nat) (R : Finset Nat)
    (inside : Fin m → Fin m → Bool) : Fin m → Fin m → Bool :=
  fun i j =>
    if i.val ∈ R ∧ j.val ∈ R then inside i j else false

/-- The generic extension step with disjoint constraints (C1) and (C2). -/
theorem exists_extension_zero_outside
    (G : GenericEnumerated3Graph)
    (m : Nat) (R : Finset Nat)
    (inside : Fin m → Fin m → Bool) :
    ∃ v : Nat, m ≤ v ∧
      (∀ i j : Fin m, i < j →
        i.val ∈ R → j.val ∈ R →
        (G.graph.edge i.val j.val v ↔ inside i j = true)) ∧
      (∀ i j : Fin m, i < j →
        (i.val ∉ R ∨ j.val ∉ R) →
        ¬G.graph.edge i.val j.val v) := by
  classical
  obtain ⟨v, hv, hpat⟩ := G.extension m (extendPattern m R inside)
  refine ⟨v, hv, ?_, ?_⟩
  · intro i j hij hi hj
    have hpair : i.val ∈ R ∧ j.val ∈ R := ⟨hi, hj⟩
    have h := hpat i j hij
    change G.graph.edge i.val j.val v ↔
      (if i.val ∈ R ∧ j.val ∈ R then inside i j else false) = true at h
    simpa only [if_pos hpair] using h
  · intro i j hij hout hEdge
    have hnot : ¬ (i.val ∈ R ∧ j.val ∈ R) := by
      intro hp
      rcases hout with hi | hj
      · exact hi hp.1
      · exact hj hp.2
    have hp : extendPattern m R inside i j = false := by
      simp only [extendPattern, if_neg hnot]
    have h : extendPattern m R inside i j = true :=
      (hpat i j hij).mp hEdge
    rw [hp] at h
    cases h

end GenericEnumerated3Graph
end ThreeUniformDiaries
