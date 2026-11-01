import ThreeUniformDiaries.DiaryPrediaryDefinition

/-!
# Track B: the actual shifted three-marker pre-diary seed

The proof of manuscript thm:amend adds three role/Devlin markers in
front of an arbitrary enumerated 3-hypergraph. This module records
the precise edge table and proves all elementary V/E conditions,
the induced shifted leaf reduct and exact leaf census.

The remaining substantive seed gate is preservation of the true
lexicographic comparison after adding Devlin marker edges. We do
NOT assume that follows from the marker assignment by definition:
the new edges can affect source type meets. Instead state this
single remaining obligation explicitly as a hypothesis in the
RolePrediary constructor. Finite adversarial regressions for the
unconditional claim are checked separately by CI (#1014).

This does not use or validate the false universal old-cut
preservation clause in the printed pre-diary completion lemma,
nor does it assert the final countable diary existence theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Insert three new markers, shift every original old hyperedge,
and assign the two Devlin marker bits by the ORIGINAL source
LexEarlier comparison. All edges are increasing triples. -/
noncomputable def shiftedDiarySeed
    (H : Ordered3Graph Nat) : Ordered3Graph Nat where
  edge x y z :=
    x < y ∧ y < z ∧
      ((3 ≤ x ∧ H.edge (x-3) (y-3) (z-3)) ∨
       (x = 1 ∧ 3 ≤ y ∧ LexEarlier H (y-3) (z-3)) ∨
       (x = 2 ∧ 3 ≤ y ∧ ¬ LexEarlier H (y-3) (z-3)))

/-- Every original increasing triple is induced, with both
hyperedges AND nonedges, on shifted old vertices. -/
theorem shiftedDiarySeed_leaf_edge_iff
    (H : Ordered3Graph Nat)
    (a b c : Nat) (hab : a < b) (hbc : b < c) :
    (shiftedDiarySeed H).edge (a+3) (b+3) (c+3) ↔
      H.edge a b c := by
  have hAB : a + 3 < b + 3 := by omega
  have hBC : b + 3 < c + 3 := by omega
  have hA3 : 3 ≤ a + 3 := by omega
  have hA1 : a + 3 ≠ 1 := by omega
  have hA2 : a + 3 ≠ 2 := by omega
  simp only [shiftedDiarySeed, hAB, hBC, hA3, hA1, hA2,
    true_and, false_and, false_or, or_false, Nat.add_sub_cancel_right]

/-- No edge starts at marker zero, so all old vertices have
the true leaf role, not a role guessed from an extra predicate. -/
theorem shiftedDiarySeed_no_zero_edge
    (H : Ordered3Graph Nat) (y z : Nat) :
    ¬ (shiftedDiarySeed H).edge 0 y z := by
  simp [shiftedDiarySeed]

theorem shiftedDiarySeed_old_isLeaf
    (H : Ordered3Graph Nat) (u : Nat) (hu : 3 ≤ u) :
    IsLeaf (shiftedDiarySeed H) u := by
  exact ⟨hu,shiftedDiarySeed_no_zero_edge H 1 u,
    shiftedDiarySeed_no_zero_edge H 2 u⟩

/-- Exactly the three markers are not leaves in the raw seed.
In particular no unintended leaf is ever inserted here. -/
theorem shiftedDiarySeed_leaf_iff
    (H : Ordered3Graph Nat) (u : Nat) :
    IsLeaf (shiftedDiarySeed H) u ↔ 3 ≤ u := by
  constructor
  · exact fun h => h.1
  · exact shiftedDiarySeed_old_isLeaf H u

/-- Exact first Devlin marker bit in the source construction. -/
theorem shiftedDiarySeed_marker_one_iff
    (H : Ordered3Graph Nat)
    (a b : Nat) (ha : 3 ≤ a) (hab : a < b) :
    (shiftedDiarySeed H).edge 1 a b ↔
      LexEarlier H (a-3) (b-3) := by
  have h1a : 1 < a := by omega
  simp [shiftedDiarySeed, h1a, hab, ha]

/-- Exact complementary second Devlin marker bit. -/
theorem shiftedDiarySeed_marker_two_iff
    (H : Ordered3Graph Nat)
    (a b : Nat) (ha : 3 ≤ a) (hab : a < b) :
    (shiftedDiarySeed H).edge 2 a b ↔
      ¬ LexEarlier H (a-3) (b-3) := by
  have h2a : 2 < a := by omega
  simp [shiftedDiarySeed, h2a, hab, ha]

/-- Except for V3, all source V/E clauses are forced by the
literal seed construction. The only additional hypothesis says
the actual destination LexEarlier is the transported source one.

This is strictly weaker than assuming any global type agreement
or preserving all capped 1- and 2-type meets. -/
theorem shiftedDiarySeed_isPrediary_of_lex
    (H : Ordered3Graph Nat)
    (hLex : ∀ a b : Nat, a < b →
      (LexEarlier (shiftedDiarySeed H) (a+3) (b+3) ↔
       LexEarlier H a b)) :
    RolePrediary (shiftedDiarySeed H) := by
  let P := shiftedDiarySeed H
  have hNone : ∀ y z, ¬ P.edge 0 y z :=
    shiftedDiarySeed_no_zero_edge H
  have hLeaf : ∀ u, 3 ≤ u → IsLeaf P u :=
    shiftedDiarySeed_old_isLeaf H
  refine {
    role_valid := ?_
    one_split_coherent := ?_
    one_split_witness := ?_
    two_split_coherent := ?_
    two_split_witness := ?_
    leaf_marker_one := ?_
    leaf_marker_two := ?_
    edge_ordered := ?_
    permitted_edge := ?_
  }
  · intro u hu
    exact Or.inl (hLeaf u hu)
  · intro m a b hm _ _ _ _
    exact False.elim (hNone 1 m hm.2.1)
  · intro m hm
    exact False.elim (hNone 1 m hm.2.1)
  · intro m a b c d hm _ _ _ _ _ _ _ _
    exact False.elim (hNone 2 m hm.2.2)
  · intro m hm
    exact False.elim (hNone 2 m hm.2.2)
  · intro a b hab ha _
    have hSource : LexEarlier H (a-3) (b-3) ↔
        LexEarlier P a b := by
      have ha3 : 3 ≤ a := ha.1
      have hb3 : 3 ≤ b := by omega
      have hlt : a - 3 < b - 3 := by omega
      have h := hLex (a-3) (b-3) hlt
      simpa only [Nat.sub_add_cancel ha.1,
        Nat.sub_add_cancel (show 3 ≤ b by omega)]
        using h.symm
    exact (shiftedDiarySeed_marker_one_iff H a b ha.1 hab).trans hSource
  · intro a b hab ha _
    have hSource : LexEarlier H (a-3) (b-3) ↔
        LexEarlier P a b := by
      have ha3 : 3 ≤ a := ha.1
      have hb3 : 3 ≤ b := by omega
      have hlt : a - 3 < b - 3 := by omega
      have h := hLex (a-3) (b-3) hlt
      simpa only [Nat.sub_add_cancel ha.1,
        Nat.sub_add_cancel (show 3 ≤ b by omega)]
        using h.symm
    exact (shiftedDiarySeed_marker_two_iff H a b ha.1 hab).trans
      (not_congr hSource)
  · intro x y z he
    exact ⟨he.1,he.2.1⟩
  · intro x y z he
    obtain ⟨hxy,hyz,hcase⟩ := he
    rcases hcase with hOld | hOne | hTwo
    · right; right; right; right
      exact ⟨hLeaf x hOld.1,
        hLeaf y (by omega),hLeaf z (by omega)⟩
    · right; right; right; left
      exact ⟨Or.inl hOne.1,hLeaf y hOne.2.1,
        hLeaf z (by omega)⟩
    · right; right; right; left
      exact ⟨Or.inr hTwo.1,hLeaf y hTwo.2.1,
        hLeaf z (by omega)⟩

end DiaryLeafPriority
end ThreeUniformDiaries
