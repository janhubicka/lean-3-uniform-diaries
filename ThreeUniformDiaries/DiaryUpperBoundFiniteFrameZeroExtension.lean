import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.InfinitePrefixes
import ThreeUniformDiaries.TypeRepresentation

/-!
# Track A: zero extension of a genuine bounded finite diary frame

The finite marked-ATR universe uses the canonical source
`EnumNode m`, represented as an ordered graph on Nat by
zero extension. The full finite diary-support construction,
on the other hand, produces an `Ordered3Graph Nat` whose
edge table is already supported in its finite frame.

For a `FiniteDiaryEdgeFrame H m`, these two representations
are LITERALLY equal as ordered 3-graphs on Nat. The proof
uses the frame's global increasing edge-support property and
the exact actual initial-segment edge lemma, not any
unverified assumption about arbitrary source tails.

This is the representation identity needed to compare the
V/E/S axioms of a finite leaf-generated support with the
typed `EnumNode` source of the actual ATR finite embedding
and the genuine marked-diary classification.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- A finite V/E edge frame is identical to its canonical
m-vertex EnumNode, zero-extended on Nat. In particular
there are no false non-increasing/outside edges in the
representation used by a finite ATR source code. -/
theorem FiniteDiaryEdgeFrame.initialSegment_zeroExtension_eq
    {H : Ordered3Graph Nat} {m : Nat}
    (F : FiniteDiaryEdgeFrame H m) :
    (H.initialSegment m).toOrdered3Graph = H := by
  have hEdge :
      (H.initialSegment m).toOrdered3Graph.edge = H.edge := by
    funext a b c
    apply propext
    constructor
    · intro h
      have ht : (H.initialSegment m).triple a b c = true := h
      have hOrder : a < b ∧ b < c ∧ c < m := by
        by_contra hn
        have hBad := (H.initialSegment m).support a b c hn
        rw [hBad] at ht
        cases ht
      exact (H.initialSegment_edge_iff
        hOrder.1 hOrder.2.1 hOrder.2.2).mp ht
    · intro he
      obtain ⟨hab,hbc,_,hcm⟩ := F.edge_support a b c he
      exact (H.initialSegment_edge_iff hab hbc hcm).mpr he
  change (Ordered3Graph.mk
      (H.initialSegment m).toOrdered3Graph.edge) =
    (Ordered3Graph.mk H.edge)
  exact congrArg Ordered3Graph.mk hEdge

/-- In particular, every genuine finite full diary is exactly
its canonical finite EnumNode graph, not merely related by an
unspecified induced embedding. -/
theorem FiniteRoleDiaryBlock.zeroExtended_source_eq
    {H : Ordered3Graph Nat} {m : Nat}
    (D : FiniteRoleDiaryBlock H m) :
    (H.initialSegment m).toOrdered3Graph = H :=
  D.prediary.frame.initialSegment_zeroExtension_eq

end DiaryLeafPriority
end ThreeUniformDiaries
