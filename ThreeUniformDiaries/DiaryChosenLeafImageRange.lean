import ThreeUniformDiaries.DiaryChosenPreembedding

/-!
# The chosen pre-embedding maps source leaves into the original outer image

The lower-bound lemma requires the pre-embedding's image of the
source leaf set to lie inside the image of the original embedding
f of the generic hypergraph. The external embedding is generally
UNORDERED; its image in the target diary is fixed.

The actual candidate sends every source leaf u to the stabilised
composite F(g(ψu)), where g is the verified generic I1/I2/I3
fusion. This is literally a value of the original F, and so
the required inclusion of the leaf images is immediate.

No assertion about images of the split vertices is needed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding
open ATRFiniteDecoder

variable {H : Ordered3Graph Nat}

/-- Every SOURCE LEAF has its chosen target image in the range
of the original unordered outer embedding F. This is the exact
range clause of the manuscript's pre-embedding lemma. -/
theorem chosenPreembedding_leaf_mem_outer_range
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (u : Nat) (hu : IsLeaf H u) :
    ∃ t, D.chosenPreembedding G K F ψ u = F t := by
  refine ⟨orderedDiaryFusion G K F.toFun F.injective (ψ u), ?_⟩
  calc
    D.chosenPreembedding G K F ψ u =
      stabilisedSource G K F ψ u :=
        D.chosenPreembedding_leaf G K F ψ u hu
    _ = F (orderedDiaryFusion G K F.toFun F.injective (ψ u)) :=
        stabilisedOrdered_apply G K F (ψ u)

/-- Package the entire source LEAF image inclusion under the
original unordered outer map, without selecting a new witness
for each leaf. -/
theorem chosenPreembedding_leaf_range_subset
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph) :
    ∀ u, IsLeaf H u →
      ∃ t, D.chosenPreembedding G K F ψ u = F t := by
  intro u hu
  exact D.chosenPreembedding_leaf_mem_outer_range G K F ψ u hu

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
