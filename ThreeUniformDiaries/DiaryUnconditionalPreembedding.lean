import ThreeUniformDiaries.DiaryGlobalOrientationFromFourTail
import ThreeUniformDiaries.DiaryPreembeddingSpec
import ThreeUniformDiaries.DiaryGenericFixedTwoEmbedding

/-!
# The complete diary pre-embedding lemma from native I3 and four tails

Once the opposite-class four-tail calibration is available, the
marker-1 relative-orientation condition in the already proved
conditional pre-embedding interface follows automatically for
every pair of ordered leaf pairs. All other pre-embedding
conditions were verified separately from the V/E/S diary axioms
and the fused I1/I2/I3 map.

This module combines these results without any extra geometric
hypothesis, then chooses the generic diary copy furnished by the
verified fixed-two K_I theorem. The outer unordered embedding
is assumed to send generic vertices to target diary leaves,
exactly as in the manuscript's pre-embedding lemma.

The statement does not assert flip absorption or complete
unavoidability, which remain subsequent steps.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding
open ATRFiniteDecoder

variable {H : Ordered3Graph Nat}

/-- No orientation witness hypothesis is needed in the complete
pre-embedding specification: finite four-tail calibration
provides it unconditionally for genuine role diaries. -/
theorem chosenPreembedding_spec_and_leaf_range
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting) :
    DiaryPreembeddingSpec H K
        (D.chosenPreembedding G K F ψ) ∧
      ∀ u, IsLeaf H u →
        ∃ t, D.chosenPreembedding G K F ψ u = F t := by
  have hrelative :
      ∀ a b c d : Nat,
        a < b → c < d →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        H.twoMeetLevel a b c d = 1 →
        ((LexEarlier H a b ↔ LexEarlier H c d) ↔
          (LexEarlier K (stabilisedSource G K F ψ a)
              (stabilisedSource G K F ψ b) ↔
           LexEarlier K (stabilisedSource G K F ψ c)
              (stabilisedSource G K F ψ d))) := by
    intro a b c d hab hcd ha hb hc hd _
    exact D.stabilisedSource_global_relative_orientation
      G K F ψ hψ
      ⟨a, b, hab, ha, hb⟩ ⟨c, d, hcd, hc, hd⟩
  exact D.chosenPreembedding_spec_and_leaf_range_of_relative_orientation
    G K F hFleaf E ψ hψ hrelative

/-- Full existential diary pre-embedding theorem: given an
unordered embedding of the enumerated generic 3-hypergraph
into the leaf-induced target diary, there is an increasing
role-preserving diary pre-embedding whose leaf images all
belong to the original outer embedding's image. -/
theorem exists_preembedding_into_leaf_range
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (hFleaf : ∀ t, IsLeaf K (F t))
    (D : RoleDiary H) (E : RoleDiary K) :
    ∃ θ : Nat → Nat,
      DiaryPreembeddingSpec H K θ ∧
        (∀ u, IsLeaf H u → ∃ t, θ u = F t) := by
  obtain ⟨ψ, hψ, _, _⟩ :=
    exists_typeRespecting_embedding_fix_two G H
  exact ⟨D.chosenPreembedding G K F ψ,
    D.chosenPreembedding_spec_and_leaf_range
      G K F hFleaf E ψ hψ⟩

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
