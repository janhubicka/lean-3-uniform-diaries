import ThreeUniformDiaries.DiaryUnorderedEmbedding
import ThreeUniformDiaries.DiaryFiveVertexOrientationGadget

/-!
# The five-vertex orientation gadget under an unordered outer embedding

This module discharges the two explicit edge/nonedge assumptions
from the preceding five-vertex orientation calculation. The outer
map F is a genuine induced embedding of the UNORDERED 3-hypergraph,
not assumed monotone. The I1-verified fused generic refinement g
makes F ∘ g strictly increasing, and therefore F ∘ g ∘ ψ is an
ordinary order-preserving induced embedding of the five-vertex
gadget. The I2 theorem simultaneously provides the close singleton
types of the two relevant gadget vertices.

This completes the isolated mathematical five-vertex orientation
calculation as actually needed by the diary lower-bound argument.
The remaining step is to derive the universal cut-zero
synchronisation statement for *arbitrary pairs* from suitable
diary-controlled placements of this finite configuration.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Once an arbitrary unordered external embedding F is refined by
the actual I1/I2-verified diary fusion, the orientation of the pair
(2,3) in any type-respecting copy of the five-vertex gadget equals
the orientation of (4,3). No additional target edge assumptions:
they follow from F being a genuine unordered hypergraph embedding. -/
theorem fiveVertex_orientation_under_unordered_embedding
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (ψ : Embedding fiveVertexOrientationGadget G.graph)
    (hψ : ψ.TypeRespecting) :
    DiaryLeafPriority.LexEarlier K
      (F (orderedDiaryFusion G K F.toFun F.injective (ψ 2)))
      (F (orderedDiaryFusion G K F.toFun F.injective (ψ 3))) ↔
    DiaryLeafPriority.LexEarlier K
      (F (orderedDiaryFusion G K F.toFun F.injective (ψ 4)))
      (F (orderedDiaryFusion G K F.toFun F.injective (ψ 3))) := by
  let g := orderedDiaryFusion G K F.toFun F.injective
  have hOrder : StrictMono (fun t => F (g t)) :=
    (orderedDiaryFusion_complete_native_stabilisation
      G K F.toFun F.injective).2.1
  let φ : Embedding fiveVertexOrientationGadget K :=
    F.orderedComposite g hOrder ψ
  have hclose : K.SameOneTypeBelow
      (φ 1 + 1) (φ 2) (φ 4) := by
    change K.SameOneTypeBelow
      (F (g (ψ 1)) + 1) (F (g (ψ 2))) (F (g (ψ 4)))
    exact fiveVertex_gadget_close_types_after_fusion
      G K F.toFun F.injective ψ hψ
  have h := K.fiveVertex_orientation_of_embedding φ hclose
  change DiaryLeafPriority.LexEarlier K
      (F (g (ψ 2))) (F (g (ψ 3))) ↔
    DiaryLeafPriority.LexEarlier K
      (F (g (ψ 4))) (F (g (ψ 3))) at h
  exact h

end ATRFiniteDecoder
end ThreeUniformDiaries
