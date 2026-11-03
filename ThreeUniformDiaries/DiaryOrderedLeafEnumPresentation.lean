import ThreeUniformDiaries.DiaryOrderedLeafPresentationTransport

/-!
# Track C: literal ordered EnumNode of a genuine diary leaf reduct

The manuscript defines a diary of an ORDERED finite hypergraph by
requiring its increasing leaf reduct to be order-isomorphic to the
finite source. Track C already proved that a genuine complete marking
produces a canonical permutation of A's vertices matching the
increasing order of all genuine diary leaves.

Here we package that increasing leaf reduct as an exact finite
EnumNode, and compare its actual increasing ternary edge table to
the permutation presentation of A. This is a finite literal
representation bridge, not an assumed isomorphism of raw diagrams.

No Ramsey theorem, countable diary construction, source-cover
assumption, or unavoidability is used.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- The exact finite ordered leaf reduct of a finite enumerated
source, represented as an EnumNode after increasing reindexing.
The specified equality certifies the number of genuine leaves.
Only strictly increasing triples within that finite frame can
be hyperedges. -/
noncomputable def ProtectedSource.increasingLeafEnum
    (S : ProtectedSource 0)
    (a : Nat) (hCard : S.leafPositions.card = a) :
    EnumNode a where
  triple i j k :=
    if h : i < j ∧ j < k ∧ k < a then
      S.picture.triple
        (((S.leafPositions.orderIsoOfFin hCard)
          ⟨i, by omega⟩).val).val
        (((S.leafPositions.orderIsoOfFin hCard)
          ⟨j, by omega⟩).val).val
        (((S.leafPositions.orderIsoOfFin hCard)
          ⟨k, by omega⟩).val).val
    else false
  support := by
    intro i j k hbad
    simp [hbad]

/-- Every increasing source triple has exactly its induced edge bit
in the increasing enumeration of the genuine leaf set. No edges
or nonedges are silently inferred from the source markings. -/
theorem ProtectedSource.increasingLeafEnum_edge_iff
    (S : ProtectedSource 0) (a : Nat)
    (hCard : S.leafPositions.card = a)
    (i j k : Fin a) (hij : i < j) (hjk : j < k) :
    (S.increasingLeafEnum a hCard).toOrdered3Graph.edge
      i.val j.val k.val ↔
    S.picture.toOrdered3Graph.unorderedEdge
      (((S.leafPositions.orderIsoOfFin hCard) i).val).val
      (((S.leafPositions.orderIsoOfFin hCard) j).val).val
      (((S.leafPositions.orderIsoOfFin hCard) k).val).val := by
  have hValid : i.val < j.val ∧ j.val < k.val ∧ k.val < a :=
    ⟨hij, hjk, k.isLt⟩
  have hltIJ :
      ((S.leafPositions.orderIsoOfFin hCard) i).val <
        ((S.leafPositions.orderIsoOfFin hCard) j).val :=
    (S.leafPositions.orderIsoOfFin hCard).strictMono hij
  have hltJK :
      ((S.leafPositions.orderIsoOfFin hCard) j).val <
        ((S.leafPositions.orderIsoOfFin hCard) k).val :=
    (S.leafPositions.orderIsoOfFin hCard).strictMono hjk
  change (if h : i.val < j.val ∧ j.val < k.val ∧ k.val < a then
      S.picture.triple
        (((S.leafPositions.orderIsoOfFin hCard)
          ⟨i.val, by omega⟩).val).val
        (((S.leafPositions.orderIsoOfFin hCard)
          ⟨j.val, by omega⟩).val).val
        (((S.leafPositions.orderIsoOfFin hCard)
          ⟨k.val, by omega⟩).val).val
      else false) = true ↔
    S.picture.toOrdered3Graph.unorderedEdge
      (((S.leafPositions.orderIsoOfFin hCard) i).val).val
      (((S.leafPositions.orderIsoOfFin hCard) j).val).val
      (((S.leafPositions.orderIsoOfFin hCard) k).val).val
  rw [dif_pos hValid]
  exact (S.picture.toOrdered3Graph.unorderedEdge_iff_of_lt
    _ _ _ hltIJ hltJK).symm

/-- The genuine diary's increasing leaf reduct is a LITERAL
ordered presentation of the underlying unordered hypergraph A:
its increasing edge relation agrees with A after the exact
inverse marking-rank permutation constructed in Track C #1050.

Unlike the more abstract ordered-signature partition, this
statement checks the actual finite EnumNode edge predicate. -/
theorem genuineMarkedDiaryShape_increasingLeafEnum_presentation
    {a : Nat} (A : EnumNode a)
    (T : MarkedFiniteSource 0 a)
    (hShape : IsGenuineMarkedDiaryShape A T)
    (i j k : Fin a) (hij : i < j) (hjk : j < k) :
    (T.source.increasingLeafEnum a
      (genuineMarkedDiaryShape_leafPositions_card A T hShape)).toOrdered3Graph.edge
      i.val j.val k.val ↔
    A.toOrdered3Graph.unorderedEdge
      ((genuineMarkedDiaryShape_labelRankPerm A T hShape).symm i).val
      ((genuineMarkedDiaryShape_labelRankPerm A T hShape).symm j).val
      ((genuineMarkedDiaryShape_labelRankPerm A T hShape).symm k).val := by
  have hEnum :=
    T.source.increasingLeafEnum_edge_iff a
      (genuineMarkedDiaryShape_leafPositions_card A T hShape)
      i j k hij hjk
  have hPresented :=
    genuineMarkedDiaryShape_increasing_presentation A T hShape i j k
  exact hEnum.trans hPresented.symm

end ATRFiniteDecoder
end ThreeUniformDiaries
