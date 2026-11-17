import ThreeUniformDiaries.DiaryCanonicalMarkedRestrictionTransport
import ThreeUniformDiaries.DiaryUpperBoundFiniteFrameZeroExtension

/-!
# Raw canonical restriction: source size and exact induced picture

The intrinsic raw restriction of a finite marked source is a
literal marked finite source. Its full source picture is the
canonical increasing induced graph on its selected leaf-meet
support, not merely an isomorphic finite graph.

The first lemma is independent of diary axioms: any finite
increasing induced support is already zero outside its frame.
The subsequent two lemmas expose the constructor data needed
to compare with a canonical marked B-source in a full RoleDiary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Canonical finite induced support graphs are already
zero-extended; their initial-segment EnumNode representation
recovers the EXACT graph, for every ordered ternary source. -/
theorem finiteSupportGraph_zeroExtended_eq
    (G : Ordered3Graph Nat) (S : Finset Nat) :
    ((finiteSupportGraph G S).initialSegment S.card).toOrdered3Graph =
      finiteSupportGraph G S := by
  let H := finiteSupportGraph G S
  have hEdges : (H.initialSegment S.card).toOrdered3Graph.edge =
      H.edge := by
    funext a b c
    apply propext
    constructor
    · intro h
      have ht : (H.initialSegment S.card).triple a b c = true := h
      have hOrder : a < b ∧ b < c ∧ c < S.card := by
        by_contra hn
        have hBad := (H.initialSegment S.card).support a b c hn
        rw [hBad] at ht
        cases ht
      exact (H.initialSegment_edge_iff
        hOrder.1 hOrder.2.1 hOrder.2.2).mp ht
    · intro he
      obtain ⟨hab,hbc,hc⟩ :=
        finiteSupportGraph_edge_ordered G S a b c he
      exact (H.initialSegment_edge_iff hab hbc hc).mpr he
  change Ordered3Graph.mk (H.initialSegment S.card).toOrdered3Graph.edge =
    Ordered3Graph.mk H.edge
  exact congrArg Ordered3Graph.mk hEdges

end DiaryLeafPriority

namespace ATRFiniteDecoder
open DiaryLeafPriority

/-- Changing a dependent EnumNode size index along an equality
does not change its zero-extended ordered ternary graph. -/
theorem EnumNode.toOrdered3Graph_cast
    {n m : Nat} (h : n = m) (E : EnumNode m) :
    (h.symm ▸ E).toOrdered3Graph = E.toOrdered3Graph := by
  cases h
  rfl

/-- The raw restriction's size is exactly the finite S1/S2
support cardinality, not a loose upper bound. -/
theorem MarkedFiniteSource.rawRestrict_source_size
    {a b : Nat} (P : MarkedFiniteSource 0 a)
    (i : Fin b → Fin a) :
    (P.rawRestrict i).source.k + 1 =
      (markedRestrictionSupport P i).card := by
  classical
  unfold MarkedFiniteSource.rawRestrict
  dsimp [markedRestrictionSupport]
  have hCard : 3 ≤
      (finiteLeafMeetSupport P.source.picture.toOrdered3Graph
        (markedRestrictionLeaves P i)).card :=
    (finiteLeafMeetSupport_reindex_markers
      P.source.picture.toOrdered3Graph
      (markedRestrictionLeaves P i)).1
  omega

/-- The complete graph table of the raw restricted code is
the canonical finite induced graph of its selected support. -/
theorem MarkedFiniteSource.rawRestrict_source_graph
    {a b : Nat} (P : MarkedFiniteSource 0 a)
    (i : Fin b → Fin a) :
    (P.rawRestrict i).source.picture.toOrdered3Graph =
      finiteSupportGraph P.source.picture.toOrdered3Graph
        (markedRestrictionSupport P i) := by
  classical
  let H : Ordered3Graph Nat := P.source.picture.toOrdered3Graph
  let L : Finset Nat := markedRestrictionLeaves P i
  let S : Finset Nat := finiteLeafMeetSupport H L
  have hCard : 1 ≤ S.card := by
    exact (by decide : 1 ≤ 3).trans
      (finiteLeafMeetSupport_reindex_markers H L).1
  have hk : S.card - 1 + 1 = S.card :=
    Nat.sub_add_cancel hCard
  change (hk.symm ▸ (finiteSupportGraph H S).initialSegment S.card).toOrdered3Graph =
    finiteSupportGraph H S
  exact (EnumNode.toOrdered3Graph_cast hk _).trans
    (finiteSupportGraph_zeroExtended_eq H S)

end ATRFiniteDecoder
end ThreeUniformDiaries
