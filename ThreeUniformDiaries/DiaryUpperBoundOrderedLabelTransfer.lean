import ThreeUniformDiaries.DiaryFiniteAutTorsor
import ThreeUniformDiaries.DiaryUpperBoundDirectTransfer

/-!
# Track A: ordered induced embeddings preserve arbitrary labelled copies

The direct upper-bound argument embeds the original universal
hypergraph into the leaf reduct of a full diary, then embeds the
whole diary into the enumerated generic 3-hypergraph.

The vertex maps in these two steps are strictly increasing and
induced on increasing triples, but an individual labelled copy of
A may arrive with its labels in ANY numerical order. Therefore the
corresponding composed tuple must be shown to preserve the fully
symmetric underlying 3-hyperedge predicate on every triple.

This is a purely relational consequence of the induced embedding
and its strict monotonicity. It does not require any diary role,
Ramsey, unavoidability or completion hypothesis.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

namespace Embedding

/-- A globally strictly increasing induced ordered 3-graph
embedding preserves and reflects the symmetric underlying
hyperedge relation on ALL triples, including repeated vertices.
No source enumeration order restriction is needed. -/
theorem unorderedEdge_iff_all
    {H K : Ordered3Graph Nat}
    (f : Embedding H K) (a b c : Nat) :
    H.unorderedEdge a b c ↔
      K.unorderedEdge (f a) (f b) (f c) := by
  have hlt (u v : Nat) : u < v ↔ f u < f v := by
    constructor
    · exact f.strictMono
    · intro huv
      by_contra hnot
      exact (not_lt_of_ge (f.strictMono.monotone
        (Nat.le_of_not_gt hnot))) huv
  have hTriple (u v w : Nat) :
      (u < v ∧ v < w ∧ H.edge u v w) ↔
        (f u < f v ∧ f v < f w ∧
          K.edge (f u) (f v) (f w)) := by
    constructor
    · rintro ⟨huv,hvw,he⟩
      exact ⟨(hlt u v).mp huv, (hlt v w).mp hvw,
        (f.edge_iff huv hvw).mp he⟩
    · rintro ⟨huv,hvw,he⟩
      have huv' := (hlt u v).mpr huv
      have hvw' := (hlt v w).mpr hvw
      exact ⟨huv',hvw', (f.edge_iff huv' hvw').mpr he⟩
  unfold unorderedEdge
  exact or_congr (hTriple a b c)
    (or_congr (hTriple a c b)
      (or_congr (hTriple b a c)
        (or_congr (hTriple b c a)
          (or_congr (hTriple c a b) (hTriple c b a)))))

end Embedding

/-- The prescribed labelled induced A-copy can be transported
through any ordered induced embedding even if the labels and
their images are not increasing. -/
theorem IsFiniteLabelledCopy.map_orderedEmbedding
    {H K A : Ordered3Graph Nat} {n : Nat}
    (f : Embedding H K)
    (v : Fin n → Nat)
    (hv : IsFiniteLabelledCopy A H n v) :
    IsFiniteLabelledCopy A K n (fun i => f (v i)) := by
  refine ⟨f.strictMono.injective.comp hv.1, ?_⟩
  intro i j k
  exact (hv.2 i j k).trans
    (f.unorderedEdge_iff_all (v i) (v j) (v k))

end Ordered3Graph
end ThreeUniformDiaries
