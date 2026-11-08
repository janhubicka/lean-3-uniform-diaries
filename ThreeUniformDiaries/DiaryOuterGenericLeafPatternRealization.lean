import ThreeUniformDiaries.DiaryFiniteUniversalLeafRange
import ThreeUniformDiaries.DiarySingletonColourCofinalCone

/-!
# Track D: genuine finite leaf-only pattern realization in an unordered generic range

Fix an arbitrary UNORDERED induced embedding F of the enumerated
generic 3-hypergraph G into the target ordered ternary graph K.
The original leaf range F[G] need not be increasing in the
target enumeration. In particular, a source initial segment is
not in general a target initial segment.

Given a finite target cut B, a numerical lower bound M and ANY
Boolean incidence pattern on unordered target pairs, the intrinsic
generic finite-extension property yields a new vertex F(t)>M
realizing exactly that pattern on ALL target-ordered pairs from
F[G] below B, including requested NONEDGES.

The subtle finite step is to use injectivity of F to bound the
source preimages of a finite target interval, then translate the
target-ordered pattern back through either source pair orientation.
The verified six-permutation unordered-embedding transport
guarantees that the edge and nonedge answers are exact.

This establishes the genuine LEAF-LEAF-NEW-LEAF part of relative
realization in a fixed generic subcopy. It does NOT control mixed
tests with target markers or splits, full S1/S2 numeric meets,
future-order reserve, or the actual next-leaf persistence gate.
For an arbitrary universal U containing G, the statement is only
about the selected generic subcopy F[G], not every vertex of F[U].
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- A completely arbitrary finite edge/nonedge pattern on target
pairs drawn from the image of the generic hypergraph can be
realized by an arbitrarily late new target vertex in the SAME
original unordered generic image.

There is no assumption that F is increasing. The mask chi is
evaluated with the target pair in INCREASING order, independently
of the enumeration order of its source preimages. -/
theorem exists_outer_generic_vertex_realizing_bounded_pair_pattern
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (B M : Nat) (chi : Nat → Nat → Bool) :
    ∃ t : Nat, M < F t ∧
      ∀ i j : Nat, F i < F j → F j < B →
        (K.edge (F i) (F j) (F t) ↔
          chi (F i) (F j) = true) := by
  classical
  obtain ⟨N, hLarge⟩ :=
    injective_nat_eventually_above_bound
      F.toFun F.injective (max B M)
  let pattern : Fin N → Fin N → Bool := fun x y =>
    if F x.val < F y.val then
      chi (F x.val) (F y.val)
    else chi (F y.val) (F x.val)
  obtain ⟨w, hwN, hPattern⟩ := G.extension N pattern
  have hHigh : max B M < F w := hLarge w hwN
  have hwM : M < F w := by omega
  refine ⟨w, hwM, ?_⟩
  intro i j hTargetOrder hjB
  have hiB : F i < B := lt_trans hTargetOrder hjB
  have hiN : i < N := by
    by_contra hNot
    have hBad : max B M < F i := hLarge i (by omega)
    omega
  have hjN : j < N := by
    by_contra hNot
    have hBad : max B M < F j := hLarge j (by omega)
    omega
  have hiw : i < w := by omega
  have hjw : j < w := by omega
  have hjFw : F j < F w := by omega
  let ii : Fin N := ⟨i, hiN⟩
  let jj : Fin N := ⟨j, hjN⟩
  have hSource :
      G.graph.unorderedEdge i j w ↔
        chi (F i) (F j) = true := by
    by_cases hij : i < j
    · have hfin : ii < jj := hij
      have hPatternVal : pattern ii jj = chi (F i) (F j) := by
        simp [pattern, ii, jj, hTargetOrder]
      calc
        G.graph.unorderedEdge i j w ↔ G.graph.edge i j w :=
          G.graph.unorderedEdge_iff_of_lt i j w hij hjw
        _ ↔ pattern ii jj = true := hPattern ii jj hfin
        _ ↔ chi (F i) (F j) = true := by rw [hPatternVal]
    · have hji : j < i := by
        have hne : i ≠ j := by
          intro h
          subst j
          exact (lt_irrefl _) hTargetOrder
        omega
      have hfin : jj < ii := hji
      have hNoReverse : ¬ F j < F i :=
        not_lt_of_ge hTargetOrder.le
      have hPatternVal : pattern jj ii = chi (F i) (F j) := by
        simp [pattern, ii, jj, hNoReverse]
      calc
        G.graph.unorderedEdge i j w ↔
            G.graph.unorderedEdge j i w :=
          G.graph.unorderedEdge_swap_first i j w
        _ ↔ G.graph.edge j i w :=
          G.graph.unorderedEdge_iff_of_lt j i w hji hiw
        _ ↔ pattern jj ii = true := hPattern jj ii hfin
        _ ↔ chi (F i) (F j) = true := by rw [hPatternVal]
  have hijNe : i ≠ j := by
    intro h
    subst j
    exact (lt_irrefl _) hTargetOrder
  have hEmbedded :
      K.unorderedEdge (F i) (F j) (F w) ↔
        chi (F i) (F j) = true :=
    (F.edge_iff_distinct i j w hijNe
      (ne_of_lt hiw) (ne_of_lt hjw)).symm.trans hSource
  exact (K.unorderedEdge_iff_of_lt
    (F i) (F j) (F w) hTargetOrder hjFw).symm.trans hEmbedded

/-- Special case: any finite set of target-ordered pairs from F[G]
can be simultaneously joined to a new vertex of arbitrarily
large target index, with every requested triple an ACTUAL edge. -/
theorem exists_outer_generic_vertex_positive_on_bounded_pairs
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K) (B M : Nat) :
    ∃ t : Nat, M < F t ∧
      ∀ i j : Nat, F i < F j → F j < B →
        K.edge (F i) (F j) (F t) := by
  obtain ⟨t, ht, hPattern⟩ :=
    exists_outer_generic_vertex_realizing_bounded_pair_pattern
      G K F B M (fun _ _ => true)
  refine ⟨t, ht, ?_⟩
  intro i j hij hjB
  exact (hPattern i j hij hjB).mpr rfl

/-- The opposite pattern is equally realizable: an arbitrarily
late vertex in the original generic range can be chosen to form
NO new triple with any target-ordered old-range pair below B. -/
theorem exists_outer_generic_vertex_negative_on_bounded_pairs
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K) (B M : Nat) :
    ∃ t : Nat, M < F t ∧
      ∀ i j : Nat, F i < F j → F j < B →
        ¬ K.edge (F i) (F j) (F t) := by
  obtain ⟨t, ht, hPattern⟩ :=
    exists_outer_generic_vertex_realizing_bounded_pair_pattern
      G K F B M (fun _ _ => false)
  refine ⟨t, ht, ?_⟩
  intro i j hij hjB hEdge
  have hFalse := (hPattern i j hij hjB).mp hEdge
  exact Bool.noConfusion hFalse

end DiaryLeafPriority
end ThreeUniformDiaries
