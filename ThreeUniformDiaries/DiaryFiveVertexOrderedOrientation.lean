import ThreeUniformDiaries.DiaryLexEarlierComplement
import ThreeUniformDiaries.DiaryFiveVertexUnorderedApplication
import ThreeUniformDiaries.DiaryUnorderedNativeStabilisation

/-!
# The five-vertex gadget gives opposite signs on increasing pairs

The published cut-zero argument begins with the induced pattern
on {0,1,2,3,4} having just the edge {0,1,3}. The previously
validated calculation yields

   LexEarlier(2,3) ↔ LexEarlier(4,3).

The right-hand comparison is in reverse enumeration order.
The general first-disagreement theorem now identifies it with
the COMPLEMENT of LexEarlier(3,4). Therefore two INCREASING
ordered pairs, (2,3) and (3,4), have opposite orientations.
This holds both in the source gadget and after the verified
type-respecting generic embedding followed by the genuinely
UNORDERED external hypergraph embedding and fused refinement.

In particular, this supplies one actual opposite-sign witness,
an important prerequisite for the remaining global orientation
synchronisation. It does not prove that all ordered leaf-pair
comparisons are connected by the necessary gadget
amalgamations, or that the global orientation dichotomy holds.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- In the concrete source five-vertex gadget, the two
INCREASING pairs (2,3) and (3,4) have opposite lexicographic
orientations. No abstract envelope equality is assumed. -/
theorem fiveVertex_source_increasing_pairs_opposite :
    DiaryLeafPriority.LexEarlier fiveVertexOrientationGadget 2 3 ↔
      ¬ DiaryLeafPriority.LexEarlier fiveVertexOrientationGadget 3 4 := by
  have hmono : StrictMono (fun t : Nat => t) := by
    intro a b hab
    exact hab
  have hnonedge : ¬ fiveVertexOrientationGadget.edge 0 1 2 := by
    simp [fiveVertexOrientationGadget]
  have hedge : fiveVertexOrientationGadget.edge 0 1 3 := by
    simp [fiveVertexOrientationGadget]
  have hclose : fiveVertexOrientationGadget.SameOneTypeBelow
      ((fun t : Nat => t) 1 + 1) 2 4 := by
    simpa using fiveVertexOrientationGadget_oneType_2_4
  have hlocal :
      DiaryLeafPriority.LexEarlier fiveVertexOrientationGadget 2 3 ↔
        DiaryLeafPriority.LexEarlier fiveVertexOrientationGadget 4 3 := by
    simpa using
      (fiveVertexOrientationGadget.fiveVertex_orientation_of_target_bits
        (fun t : Nat => t) hmono hnonedge hedge hclose)
  exact hlocal.trans
    (DiaryLeafPriority.lexEarlier_swap_complement
      fiveVertexOrientationGadget 4 3 (by omega))

end Ordered3Graph

namespace ATRFiniteDecoder

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

/-- Under the actual fused map arising from any initially UNORDERED
outer hypergraph embedding, the two increasing gadget pairs
(ψ2,ψ3), (ψ3,ψ4) have opposite target LexEarlier signs.
This follows from the separately checked local gadget equality
and the general swap-complement theorem. -/
theorem fiveVertex_increasing_pairs_opposite_after_unordered_fusion
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (ψ : Embedding fiveVertexOrientationGadget G.graph)
    (hψ : ψ.TypeRespecting) :
    let Φ := stabilisedOrdered G K F
    DiaryLeafPriority.LexEarlier K (Φ (ψ 2)) (Φ (ψ 3)) ↔
      ¬ DiaryLeafPriority.LexEarlier K (Φ (ψ 3)) (Φ (ψ 4)) := by
  let Φ := stabilisedOrdered G K F
  have hlocal : DiaryLeafPriority.LexEarlier K
      (Φ (ψ 2)) (Φ (ψ 3)) ↔
      DiaryLeafPriority.LexEarlier K
        (Φ (ψ 4)) (Φ (ψ 3)) := by
    simpa only [stabilisedOrdered_apply] using
      fiveVertex_orientation_after_unordered_fusion G K F ψ hψ
  have hlt : Φ (ψ 3) < Φ (ψ 4) :=
    Φ.strictMono (ψ.strictMono (by omega))
  have hcomplement :
      DiaryLeafPriority.LexEarlier K (Φ (ψ 4)) (Φ (ψ 3)) ↔
        ¬ DiaryLeafPriority.LexEarlier K (Φ (ψ 3)) (Φ (ψ 4)) :=
    DiaryLeafPriority.lexEarlier_swap_complement
      K (Φ (ψ 4)) (Φ (ψ 3)) (ne_of_gt hlt)
  exact hlocal.trans hcomplement

/-- Such an opposite-sign increasing-pair gadget actually exists
in every generic hypergraph, even with an arbitrary unordered
external hypergraph embedding. The proven universal countable
type-respecting embedding supplies the source copy. -/
theorem exists_fiveVertex_increasing_pairs_opposite
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K) :
    ∃ ψ : Embedding fiveVertexOrientationGadget G.graph,
      ψ.TypeRespecting ∧
      (let Φ := stabilisedOrdered G K F
       DiaryLeafPriority.LexEarlier K (Φ (ψ 2)) (Φ (ψ 3)) ↔
         ¬ DiaryLeafPriority.LexEarlier K (Φ (ψ 3)) (Φ (ψ 4))) := by
  obtain ⟨ψ, hψ⟩ := exists_typeRespecting_fiveVertex_gadget G
  exact ⟨ψ, hψ,
    fiveVertex_increasing_pairs_opposite_after_unordered_fusion
      G K F ψ hψ⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
