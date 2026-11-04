import ThreeUniformDiaries.DiaryFiniteMeetEmbedding
import ThreeUniformDiaries.DiaryUpperBoundFiniteUnorderedCopyTransfer

/-!
# Track C lower: actual labelled copies transport through finite full-meet embeddings

A full finite meet embedding is strictly increasing and preserves and
reflects all increasing ternary edges and nonedges in its genuine
source frame. Consequently it also preserves and reflects unordered
hyperedges on every three actual finite source vertices, regardless
of their order.

This closes the six-permutation labelled-copy transport used in the
canonical lower-colouring persistence argument. In particular the
source labels of A are NOT assumed to be numerically ordered in
the source diary. There is no global countable fusion, colouring,
or lower big Ramsey degree assumption here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- Under a bounded finite FULL meet embedding, the symmetric
unordered hyperedge predicate is preserved AND reflected on any
three actual finite source positions, including non-increasing
coordinate presentations. -/
theorem FiniteMeetEmbedding.unorderedEdge_iff_actual
    {H K : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}
    (E : FiniteMeetEmbedding H K n f)
    (a b c : Fin n) :
    H.unorderedEdge a.val b.val c.val ↔
      K.unorderedEdge (f a.val) (f b.val) (f c.val) := by
  have hOrder (i j : Fin n) :
      i.val < j.val ↔ f i.val < f j.val := by
    constructor
    · intro hij
      exact E.strictMono hij
    · intro h
      by_contra hn
      have hji : j.val ≤ i.val := Nat.le_of_not_gt hn
      exact (not_lt_of_ge (E.strictMono.monotone hji)) h
  have hTriple (i j k : Fin n) :
      (i.val < j.val ∧ j.val < k.val ∧
        H.edge i.val j.val k.val) ↔
      (f i.val < f j.val ∧ f j.val < f k.val ∧
        K.edge (f i.val) (f j.val) (f k.val)) := by
    constructor
    · rintro ⟨hij, hjk, he⟩
      exact ⟨(hOrder i j).mp hij,
        (hOrder j k).mp hjk,
        (E.edge_iff i.val j.val k.val hij hjk k.isLt).mpr he⟩
    · rintro ⟨hij, hjk, he⟩
      have hij' := (hOrder i j).mpr hij
      have hjk' := (hOrder j k).mpr hjk
      exact ⟨hij', hjk',
        (E.edge_iff i.val j.val k.val hij' hjk' k.isLt).mp he⟩
  unfold Ordered3Graph.unorderedEdge
  exact or_congr (hTriple a b c)
    (or_congr (hTriple a c b)
      (or_congr (hTriple b a c)
        (or_congr (hTriple b c a)
          (or_congr (hTriple c a b) (hTriple c b a)))))

/-- The entire labelled induced A-copy predicate is transported
in BOTH directions under a full finite meet embedding. The
labels are arbitrary and may occur in any source enumeration
order; the copy is a genuine injective map of Fin a, not a tuple
satisfying only a homomorphism condition. -/
theorem FiniteMeetEmbedding.labelledCopy_iff
    {H K : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}
    (E : FiniteMeetEmbedding H K n f)
    (A : Ordered3Graph Nat) (a : Nat)
    (marked : Fin a → Fin n) :
    IsFiniteLabelledCopy A H a (fun i => (marked i).val) ↔
      IsFiniteLabelledCopy A K a
        (fun i => f (marked i).val) := by
  constructor
  · intro hSource
    refine ⟨?_, ?_⟩
    · exact E.strictMono.injective.comp hSource.1
    · intro i j k
      exact (hSource.2 i j k).trans
        (E.unorderedEdge_iff_actual
          (marked i) (marked j) (marked k))
  · intro hTarget
    refine ⟨?_, ?_⟩
    · intro i j h
      apply hTarget.1
      exact congrArg f h
    · intro i j k
      exact (hTarget.2 i j k).trans
        (E.unorderedEdge_iff_actual
          (marked i) (marked j) (marked k)).symm

end DiaryLeafPriority
end ThreeUniformDiaries
