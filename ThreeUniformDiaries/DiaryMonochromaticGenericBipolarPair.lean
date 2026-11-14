import ThreeUniformDiaries.DiaryGoodColourOnePointGenericCopy
import ThreeUniformDiaries.DiarySingletonColourCofinalCone

/-!
# Track A: one SELECTED monochromatic generic pair realizes BOTH later edge bits

English-first adversarial audit: 3-uniform-diaries PR #352.

The all-prefix finite one-point colour extension condition checked
in #1484 is a sufficient but NOT a necessary criterion for a whole
generic colour class; the generic-rich bad-prefix counterexample
in PR #1490 explicitly shows n=2 failure of that overstrong condition.

Here is the correct FIRST necessary test for an ACTUAL increasing
induced generic G-selfcopy u entirely contained in a vertex class C:
the particular pair x=u(0)<y=u(1) admits arbitrarily late SAME-C
third vertices making BOTH a hyperedge and a nonedge with x,y.

Proof: the true generic extension axiom at an arbitrarily large
finite cutoff realizes a constant desired Boolean old-pair mask.
The strictly increasing induced map u transports either bit and
preserves the chosen class C.

The conclusion does NOT prove that Track D's chosen anchored
old-cut diary colour has such a pair. It is necessary, not sufficient,
for increasing generic C-richness and does not resolve future source
horizon persistence or the unordered outer target F.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

namespace GenericEnumerated3Graph

/-- For any actual old source indices a<b, any numerical bound M
and either prescribed Boolean edge bit, G has a LATER vertex v
whose (a,b,v) triple realizes exactly that bit. Both edge and
nonedge are supported by the SAME genuine generic extension axiom. -/
theorem exists_late_vertex_realizing_pair_bit
    (G : GenericEnumerated3Graph)
    (a b M : Nat) (hab : a < b) (bit : Bool) :
    ∃ v : Nat, M < v ∧ b < v ∧
      (G.graph.edge a b v ↔ bit = true) := by
  let k := max (M + 1) (b + 1)
  let pattern : Fin k → Fin k → Bool := fun _ _ => bit
  obtain ⟨v, hv, hMask⟩ := G.extension k pattern
  have haK : a < k := by
    have hbK : b < k := by
      exact lt_of_lt_of_le (Nat.lt_succ_self b)
        (le_max_right (M + 1) (b + 1))
    omega
  have hbK : b < k := by
    exact lt_of_lt_of_le (Nat.lt_succ_self b)
      (le_max_right (M + 1) (b + 1))
  have hBit :
      G.graph.edge a b v ↔ bit = true := by
    let i : Fin k := ⟨a, haK⟩
    let j : Fin k := ⟨b, hbK⟩
    have hij : i < j := hab
    have h := hMask i j hij
    simpa [i, j, pattern] using h
  refine ⟨v, ?_, ?_, hBit⟩
  · have hmK : M + 1 ≤ k := le_max_left (M + 1) (b + 1)
    omega
  · omega

end GenericEnumerated3Graph

/-- If C contains an ENTIRE increasing induced generic selfcopy,
then ONE pair of C vertices has COFINALLY MANY same-C third
vertices realizing BOTH edge and nonedge over that same pair.
The pair is SELECTED from the good copy; no condition on
other C-pairs is claimed.

This is only a necessary first finite pattern test, not a
characterization of generic richness and not an anchored
reserved-successor existence theorem. -/
theorem exists_bipolar_pair_of_monochromatic_ordered_generic_copy
    (G : GenericEnumerated3Graph)
    (C : Nat → Prop)
    (u : Ordered3Graph.Embedding G.graph G.graph)
    (hC : ∀ n : Nat, C (u n)) :
    ∃ x y : Nat,
      x < y ∧ C x ∧ C y ∧
      (∀ M : Nat, ∃ z : Nat,
        M < z ∧ y < z ∧ C z ∧
        G.graph.edge x y z) ∧
      (∀ M : Nat, ∃ z : Nat,
        M < z ∧ y < z ∧ C z ∧
        ¬ G.graph.edge x y z) := by
  have hIndexBound (n : Nat) : n ≤ u n := by
    induction n with
    | zero => omega
    | succ n ih =>
        have hStep : u n < u (n + 1) :=
          u.strictMono (Nat.lt_succ_self n)
        omega
  let x : Nat := u 0
  let y : Nat := u 1
  have hBoth (M : Nat) (bit : Bool) :
      ∃ z : Nat,
        M < z ∧ y < z ∧ C z ∧
        (G.graph.edge x y z ↔ bit = true) := by
    obtain ⟨v, hMv, h1v, hBit⟩ :=
      _root_.ThreeUniformDiaries.DiaryLeafPriority.GenericEnumerated3Graph.exists_late_vertex_realizing_pair_bit
        G 0 1 M (by omega) bit
    have hTransport :
        G.graph.edge 0 1 v ↔
          G.graph.edge (u 0) (u 1) (u v) :=
      u.edge_iff (by omega) h1v
    refine ⟨u v, ?_, u.strictMono h1v, hC v, ?_⟩
    · have hBound := hIndexBound v
      omega
    · exact hTransport.symm.trans hBit
  refine ⟨x, y, u.strictMono (by omega),
    hC 0, hC 1, ?_, ?_⟩
  · intro M
    obtain ⟨z, hM, hY, hCZ, hBit⟩ := hBoth M true
    exact ⟨z, hM, hY, hCZ, hBit.mpr rfl⟩
  · intro M
    obtain ⟨z, hM, hY, hCZ, hBit⟩ := hBoth M false
    refine ⟨z, hM, hY, hCZ, ?_⟩
    intro he
    have hAbsurd : (false : Bool) = true := hBit.mp he
    cases hAbsurd

/-- The fully UNORDERED target version needed by Track A:
if C contains an ACTUAL unordered induced generic G-copy J in an
arbitrary target ordered 3-graph K, then the fixed distinct target
pair x=J(0), y=J(1) has cofinally late SAME-C third vertices
realizing BOTH the symmetric E5 triple and its nonedge.

No monotonicity of J in target numerical order is assumed.
The elementary injective finite-preimage bound guarantees that
late source vertices map past every fixed target cutoff.
This is a NECESSARY condition for generically rich C, not a
proof that any selected anchored old-cut colour satisfies it. -/
theorem exists_unordered_bipolar_pair_of_monochromatic_generic_leaf_copy
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (C : Nat → Prop)
    (J : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hC : ∀ n : Nat, C (J n)) :
    ∃ x y : Nat,
      x ≠ y ∧ C x ∧ C y ∧
      (∀ M : Nat, ∃ z : Nat,
        M < z ∧ max x y < z ∧ C z ∧
        K.unorderedEdge x y z) ∧
      (∀ M : Nat, ∃ z : Nat,
        M < z ∧ max x y < z ∧ C z ∧
        ¬ K.unorderedEdge x y z) := by
  have hDistinct : J 0 ≠ J 1 := by
    intro h
    have h01 : (0 : Nat) = 1 := J.injective h
    omega
  have hBoth (M : Nat) (bit : Bool) :
      ∃ z : Nat,
        M < z ∧ max (J 0) (J 1) < z ∧ C z ∧
        (K.unorderedEdge (J 0) (J 1) z ↔ bit = true) := by
    obtain ⟨N, hLarge⟩ :=
      injective_nat_eventually_above_bound
        (fun n : Nat => J n) J.injective
        (max M (max (J 0) (J 1)))
    obtain ⟨v, hNv, h1v, hBit⟩ :=
      _root_.ThreeUniformDiaries.DiaryLeafPriority.GenericEnumerated3Graph.exists_late_vertex_realizing_pair_bit
        G 0 1 N (by omega) bit
    have hHigh : max M (max (J 0) (J 1)) < J v :=
      hLarge v (Nat.le_of_lt hNv)
    have hSource :
        G.graph.unorderedEdge 0 1 v ↔
          G.graph.edge 0 1 v :=
      G.graph.unorderedEdge_iff_of_lt 0 1 v (by omega) h1v
    have hTransport :
        G.graph.unorderedEdge 0 1 v ↔
          K.unorderedEdge (J 0) (J 1) (J v) :=
      J.edge_iff 0 1 v (by omega) h1v
    have hTargetBit :
        K.unorderedEdge (J 0) (J 1) (J v) ↔ bit = true :=
      hTransport.symm.trans (hSource.trans hBit)
    refine ⟨J v, ?_, ?_, hC v, hTargetBit⟩
    · exact lt_of_le_of_lt (le_max_left _ _) hHigh
    · exact lt_of_le_of_lt (le_max_right _ _) hHigh
  refine ⟨J 0, J 1, hDistinct, hC 0, hC 1, ?_, ?_⟩
  · intro M
    obtain ⟨z, hMz, hOld, hCZ, hBit⟩ := hBoth M true
    exact ⟨z, hMz, hOld, hCZ, hBit.mpr rfl⟩
  · intro M
    obtain ⟨z, hMz, hOld, hCZ, hBit⟩ := hBoth M false
    refine ⟨z, hMz, hOld, hCZ, ?_⟩
    intro he
    have hAbsurd : (false : Bool) = true := hBit.mp he
    cases hAbsurd

end DiaryLeafPriority
end ThreeUniformDiaries
