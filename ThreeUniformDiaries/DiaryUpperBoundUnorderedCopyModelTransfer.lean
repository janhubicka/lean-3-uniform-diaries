import ThreeUniformDiaries.DiaryUpperBoundLabelledCopyEquivalence

/-!
# Track A: labelled copies transport through unordered diary leaf models

The exact source-cover statement for the final upper bound is in
terms of a labelled A-copy in the original universal hypergraph U.
Its image in a full diary need only be an UNORDERED induced copy:
the diary's prescribed enumeration may differ from that of U.

The already verified `UnorderedEmbedding.edge_iff_distinct`
proves unordered edge reflection on arbitrary distinct triples,
so the labelled-copy preservation is immediate without
repeating the six-order permutation argument. The equivalence
between the two labelled-copy predicates was proved separately
(Track A #1033).

The second lemma composes the source-to-diary unordered embedding
with an ordered induced diary-to-generic embedding, obtaining the
fully labelled finite-copy predicate used in the genuine marked
source classification. No Ramsey theorem, V3 hypothesis or
countable unavoidability occurs.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- An unordered induced embedding preserves and reflects the
precise finite labelled A-copy predicate, although it need NOT
preserve the numerical ordering of the labelled vertices. -/
theorem isInducedLabelledCopy_map_unordered
    {a : Nat} (A : EnumNode a)
    {U H : Ordered3Graph Nat}
    (F : UnorderedEmbedding U H)
    (v : Fin a → Nat)
    (hv : IsInducedLabelledCopy A U v) :
    IsInducedLabelledCopy A H (fun i => F (v i)) := by
  refine ⟨F.injective.comp hv.1, ?_⟩
  intro i j k hij hjk
  have hvi : v i ≠ v j := by
    intro he
    exact (ne_of_lt hij) (hv.1 he)
  have hvik : v i ≠ v k := by
    intro he
    exact (ne_of_lt (lt_trans hij hjk)) (hv.1 he)
  have hvjk : v j ≠ v k := by
    intro he
    exact (ne_of_lt hjk) (hv.1 he)
  exact (hv.2 i j k hij hjk).trans
    (F.edge_iff_distinct (v i) (v j) (v k) hvi hvik hvjk)

/-- After the prescribed unordered source-to-leaf embedding and
a global ordered induced diary-to-generic embedding, the tuple
is a genuine fully unordered labelled A-copy in generic G.
This discharges the previously explicit `hCopyTransport` gate
of the terminal sharp upper-bound assembly, using only actual
relational embedding hypotheses. -/
theorem finiteLabelledCopy_after_diaryLeafAndGeneric
    (G : GenericEnumerated3Graph)
    (U H : Ordered3Graph Nat)
    {a : Nat} (A : EnumNode a)
    (F : UnorderedEmbedding U H)
    (η : Embedding H G.graph)
    (v : Fin a → Nat)
    (hv : IsInducedLabelledCopy A U v) :
    IsFiniteLabelledCopy A.toOrdered3Graph G.graph a
      (fun i => η (F (v i))) := by
  have hD : IsInducedLabelledCopy A H
      (fun i => F (v i)) :=
    isInducedLabelledCopy_map_unordered A F v hv
  have hG : IsInducedLabelledCopy A G.graph
      (fun i => η (F (v i))) :=
    isInducedLabelledCopy_map_unordered
      A η.asUnordered (fun i => F (v i)) hD
  exact
    (isInducedLabelledCopy_iff_fullUnordered A G.graph
      (fun i => η (F (v i)))).mp hG

end ATRFiniteDecoder
end ThreeUniformDiaries
