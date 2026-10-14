import ThreeUniformDiaries.DiaryUnorderedEmbedding
import ThreeUniformDiaries.DiaryCompleteNativeStabilisation

/-!
# The actual lower-bound stabilisation theorem for an unordered outer embedding

The outer hypergraph embedding in the manuscript is NOT initially
increasing. The verified diary type-stabilisation theorem works for
an arbitrary injective vertex map and constructs a type-respecting
generic self-embedding whose outer composite is increasing.

When the original outer map also preserves and reflects unordered
hyperedges, this increasing composite is a genuine ordered induced
embedding into the target. We package it below, together with the
full singleton and native finite pointed-pair stabilisation outputs,
as one ordinary ordered target embedding.

This is the exact bridge needed before using the target's actual
edge/nonedge pattern in the cut-zero orientation gadget and before
the pre-embedding's split-placement argument. No assumption that
the original outer map itself preserves order is introduced.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace UnorderedEmbedding

open ATRFiniteDecoder

/-- The canonically stabilised genuinely ordered target embedding
obtained from an arbitrary unordered outer hypergraph embedding. -/
noncomputable def stabilisedOrdered
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K) : Embedding G.graph K := by
  let g := orderedDiaryFusion G K F.toFun F.injective
  have horder : StrictMono (fun t => F (g t)) :=
    (orderedDiaryFusion_complete_native_stabilisation
      G K F.toFun F.injective).2.1
  exact {
    toFun := fun t => F (g t)
    strictMono := horder
    edge_iff := by
      intro a b c hab hbc
      exact F.composed_ordered_edges g horder a b c hab hbc
  }

/-- The image under the genuine ordered target embedding agrees
literally with F applied to the verified fused generic embedding. -/
theorem stabilisedOrdered_apply
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K) (t : Nat) :
    stabilisedOrdered G K F t =
      F (orderedDiaryFusion G K F.toFun F.injective t) :=
  rfl

/-- The singleton-type conclusion I2, for the ACTUAL induced ordered
target embedding obtained from the unordered outer embedding. -/
theorem stabilisedOrdered_singletonTypes
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (i : Nat) (hi : 0 < i)
    (a b : Nat) (hia : i ≤ a) (hib : i ≤ b)
    (htype : G.graph.SameOneTypeBelow i a b) :
    K.SameOneTypeBelow
      (stabilisedOrdered G K F (i-1) + 1)
      (stabilisedOrdered G K F a)
      (stabilisedOrdered G K F b) := by
  change K.SameOneTypeBelow
    (F (orderedDiaryFusion G K F.toFun F.injective (i-1)) + 1)
    (F (orderedDiaryFusion G K F.toFun F.injective a))
    (F (orderedDiaryFusion G K F.toFun F.injective b))
  exact orderedDiaryFusion_singletonType_stabilised
    G K F.toFun F.injective i hi a b hia hib htype

/-- The full native I3 conclusion for an actual unordered external
hypergraph embedding, expressed using its stabilised induced map.
The source pairs are required to share a genuine finite pointed
ATR source, as in the checked complete native theorem. -/
theorem stabilisedOrdered_pointedPairTypes
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (i a b c d : Nat) (hi : 0 < i)
    (hsource : SameFinitePointedSource G i a b c d) :
    K.SameTwoTypeBelow
      (stabilisedOrdered G K F (i-1) + 1)
      (stabilisedOrdered G K F a)
      (stabilisedOrdered G K F b)
      (stabilisedOrdered G K F c)
      (stabilisedOrdered G K F d) ∧
    (DiaryLeafPriority.LexEarlier K
      (stabilisedOrdered G K F a)
      (stabilisedOrdered G K F b) ↔
     DiaryLeafPriority.LexEarlier K
      (stabilisedOrdered G K F c)
      (stabilisedOrdered G K F d)) := by
  change
    K.SameTwoTypeBelow
      (F (orderedDiaryFusion G K F.toFun F.injective (i-1)) + 1)
      (F (orderedDiaryFusion G K F.toFun F.injective a))
      (F (orderedDiaryFusion G K F.toFun F.injective b))
      (F (orderedDiaryFusion G K F.toFun F.injective c))
      (F (orderedDiaryFusion G K F.toFun F.injective d)) ∧
    (DiaryLeafPriority.LexEarlier K
      (F (orderedDiaryFusion G K F.toFun F.injective a))
      (F (orderedDiaryFusion G K F.toFun F.injective b)) ↔
     DiaryLeafPriority.LexEarlier K
      (F (orderedDiaryFusion G K F.toFun F.injective c))
      (F (orderedDiaryFusion G K F.toFun F.injective d)))
  exact orderedDiaryFusion_I3_of_common_finite_source
    G K F.toFun F.injective i hi a b c d hsource

end UnorderedEmbedding
end Ordered3Graph
end ThreeUniformDiaries
