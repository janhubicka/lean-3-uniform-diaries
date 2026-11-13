import ThreeUniformDiaries.DiaryGenericOldE5TargetLeafRange
import ThreeUniformDiaries.DiaryFiniteUniversalLeafRange

/-!
# Track A: an entire induced generic subcopy realizes any target-ordered old E5 mask

The checked generic old-E5 fibre theorem takes a FINITE set A of
indices of the generic source G and any prescribed E5 Boolean
pattern on those indexed old pairs. In the actual relative diary
problem, however, the finite protected old leaf images are given
as TARGET NUMERICAL VERTICES, and the original external induced
generic embedding F:G→K need NOT be increasing.

Here an explicit finite-preimage cutoff translates an arbitrary
Boolean pattern chi on target-ordered old pairs F(i)<F(j)<B to the
existing generic-indexed E5 fibre theorem. In the case when
i<j and F(i)<F(j), pass chi(F(i),F(j)) directly. In the case
j<i but F(i)<F(j), reverse the source-index arguments and
use the genuine unordered edge-symmetry equivalence.

The result produces one ACTUAL induced generic target true-leaf
subcopy J:G→K within the ORIGINAL unordered F range, with ALL
J vertices above ANY chosen numerical bound M, and EVERY J
vertex realizing ALL prescribed E5 edge AND nonedge tests with
EVERY pair of actual old target leaves of F[G] below B.

No target full RoleDiary, target genericity outside F[G],
S1/S2 numeric meet, E2/E3 marker/split incidence, source diary
candidate, future reserve or countable unavoidability is used.
It is an entirely POSITIVE leaf-only geometric extension theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private theorem unorderedEdge_swap_first
    (K : Ordered3Graph Nat) (x y z : Nat) :
    K.unorderedEdge x y z ↔ K.unorderedEdge y x z := by
  unfold Ordered3Graph.unorderedEdge
  constructor
  · intro h
    rcases h with h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · intro h
    rcases h with h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- For ANY original unordered induced generic range F[G] of
actual true target leaves, ANY target numerical cutoff B, target
lower bound M and arbitrary prescribed Boolean incidence mask
chi on increasing TARGET old pairs (F i,F j) below B:

there exists one WHOLE induced unordered GENERIC subcopy J[G]
inside the original F[G] above M, whose EVERY new vertex J n
realizes exactly the requested E5 edge/nonedge bit on EVERY
target-ordered old pair from F[G] with second coordinate < B.

F and J may be non-monotone in the target enumeration. -/
theorem exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hLeaves : ∀ i : Nat, IsLeaf K (F i))
    (B M : Nat) (chi : Nat → Nat → Bool) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ B < J n ∧
        IsLeaf K (J n) ∧ ∃ t : Nat, J n = F t) ∧
      (∀ n i j : Nat, F i < F j → F j < B →
        (K.edge (F i) (F j) (J n) ↔
          chi (F i) (F j) = true)) := by
  classical
  obtain ⟨N, hHighIndex⟩ :=
    injective_nat_eventually_above_bound F F.injective B
  let A : Finset Nat := Finset.range N
  let theta : Nat → Nat → Bool := fun i j =>
    if F i < F j then chi (F i) (F j) else chi (F j) (F i)
  have hIndexBelow (i : Nat) (hiB : F i < B) : i ∈ A := by
    have hiN : i < N := by
      by_contra hn
      have hN : N ≤ i := Nat.le_of_not_gt hn
      have hAbove := hHighIndex i hN
      omega
    exact Finset.mem_range.mpr hiN
  obtain ⟨J, hRange, _hAboveOld, hPattern⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_oldE5_fibre
      G K F hLeaves A theta (max M B)
  refine ⟨J, ?_, ?_⟩
  · intro n
    obtain ⟨hLate, hLeaf, t, hF⟩ := hRange n
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hLate,
      lt_of_le_of_lt (le_max_right _ _) hLate,
      hLeaf, t, hF⟩
  · intro n i j hFiFj hFjB
    have hFiB : F i < B := lt_trans hFiFj hFjB
    have hiA : i ∈ A := hIndexBelow i hFiB
    have hjA : j ∈ A := hIndexBelow j hFjB
    have hFjJn : F j < J n := by
      obtain ⟨hLate, _hLeaf, _t, _hF⟩ := hRange n
      exact lt_of_lt_of_le hFjB
        (le_of_lt (lt_of_le_of_lt (le_max_right M B) hLate))
    have hOrdered :
        K.edge (F i) (F j) (J n) ↔
          K.unorderedEdge (F i) (F j) (J n) :=
      (K.unorderedEdge_iff_of_lt (F i) (F j) (J n)
        hFiFj hFjJn).symm
    rcases lt_trichotomy i j with hij | heq | hji
    · have hSource := hPattern n i j hiA hjA hij
      have hTail :
          K.unorderedEdge (F i) (F j) (J n) ↔
            chi (F i) (F j) = true := by
        simpa [theta, hFiFj] using hSource
      exact hOrdered.trans hTail
    · subst j
      exact False.elim ((lt_irrefl _) hFiFj)
    · have hSource := hPattern n j i hjA hiA hji
      have hFjFi : ¬ F j < F i := not_lt_of_ge hFiFj.le
      have hTail :
          K.unorderedEdge (F j) (F i) (J n) ↔
            chi (F i) (F j) = true := by
        simpa [theta, hFjFi] using hSource
      exact hOrdered.trans
        ((unorderedEdge_swap_first K (F i) (F j) (J n)).trans
          hTail)

end DiaryLeafPriority
end ThreeUniformDiaries
