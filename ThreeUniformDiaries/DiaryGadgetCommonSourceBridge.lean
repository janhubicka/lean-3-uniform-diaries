import ThreeUniformDiaries.DiaryFiveVertexOrderedOrientation
import ThreeUniformDiaries.DiaryUnorderedNativeStabilisation
import ThreeUniformDiaries.DiaryCommonFinitePointedSource

/-!
# A finite native pointed-source bridge from the five-vertex gadget

The hard remaining cut-zero orientation argument is a FINITE
amalgamation/correspondence problem, not another global Ramsey
stabilisation assertion.

Suppose two ordered pairs in the generic source, representing
the two opposite diary leaf-pair orientation classes, have
genuine common finite ATR pointed sources with the two
INCREASING pairs (2,3) and (3,4) of ONE type-respecting
five-vertex orientation gadget.

The verified native I3 theorem (for the actual F∘g ordered
embedding constructed from an UNORDERED outer map F) identifies
each pair's target lex orientation with its gadget template.
The corrected five-vertex calculation, together with the
general LexEarlier swap-complement theorem, says the two
gadget template orientations are OPPOSITE. Therefore the two
target source-pair orientations are opposite as required.

We prove this literal finite-source bridge at an arbitrary
positive cut and explicitly at cut 1. The sole remaining
geometric obligation is to produce the two native common
finite-source certificates simultaneously for a suitable
gadget copy. This is not assumed to follow automatically
from ordinary pair-type equality or from the original
abstract Env notation. No axiom, fabricated target type
preservation, or cut-zero I3 application is introduced.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace UnorderedEmbedding

open ATRFiniteDecoder

/-- Two genuine native finite pointed-source correspondences
with one five-vertex gadget force the two target lexicographic
comparisons to have opposite signs, under the ACTUAL
stabilised ordered image of any unordered outer embedding. -/
theorem oppositeLex_of_gadget_common_native_sources
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph)
    (γ : Embedding fiveVertexOrientationGadget G.graph)
    (hγ : γ.TypeRespecting)
    (i a b c d : Nat) (hi : 0 < i)
    (hplus :
      SameFinitePointedSource G i
        (ψ a) (ψ b) (γ 2) (γ 3))
    (hminus :
      SameFinitePointedSource G i
        (ψ c) (ψ d) (γ 3) (γ 4)) :
    DiaryLeafPriority.LexEarlier K
      (stabilisedOrdered G K F (ψ a))
      (stabilisedOrdered G K F (ψ b)) ↔
    ¬ DiaryLeafPriority.LexEarlier K
      (stabilisedOrdered G K F (ψ c))
      (stabilisedOrdered G K F (ψ d)) := by
  let Φ := stabilisedOrdered G K F
  have hP :
      DiaryLeafPriority.LexEarlier K (Φ (ψ a)) (Φ (ψ b)) ↔
      DiaryLeafPriority.LexEarlier K (Φ (γ 2)) (Φ (γ 3)) :=
    (stabilisedOrdered_pointedPairTypes
      G K F i (ψ a) (ψ b) (γ 2) (γ 3) hi hplus).2
  have hQ :
      DiaryLeafPriority.LexEarlier K (Φ (ψ c)) (Φ (ψ d)) ↔
      DiaryLeafPriority.LexEarlier K (Φ (γ 3)) (Φ (γ 4)) :=
    (stabilisedOrdered_pointedPairTypes
      G K F i (ψ c) (ψ d) (γ 3) (γ 4) hi hminus).2
  have hG :
      DiaryLeafPriority.LexEarlier K (Φ (γ 2)) (Φ (γ 3)) ↔
      ¬ DiaryLeafPriority.LexEarlier K (Φ (γ 3)) (Φ (γ 4)) :=
    fiveVertex_increasing_pairs_opposite_after_unordered_fusion
      G K F γ hγ
  exact hP.trans (hG.trans (not_congr hQ.symm))

/-- The same bridge expressed with the precise remaining
existence condition: a single type-respecting gadget embedding
and TWO common native ATR finite sources, one for each
ordered source pair. The conclusion itself needs no
additional pair-type or orientation hypothesis. -/
theorem oppositeLex_of_exists_gadget_common_native_sources
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph)
    (i a b c d : Nat) (hi : 0 < i)
    (hgeometry :
      ∃ γ : Embedding fiveVertexOrientationGadget G.graph,
        γ.TypeRespecting ∧
        SameFinitePointedSource G i
          (ψ a) (ψ b) (γ 2) (γ 3) ∧
        SameFinitePointedSource G i
          (ψ c) (ψ d) (γ 3) (γ 4)) :
    DiaryLeafPriority.LexEarlier K
      (stabilisedOrdered G K F (ψ a))
      (stabilisedOrdered G K F (ψ b)) ↔
    ¬ DiaryLeafPriority.LexEarlier K
      (stabilisedOrdered G K F (ψ c))
      (stabilisedOrdered G K F (ψ d)) := by
  obtain ⟨γ, hγ, hplus, hminus⟩ := hgeometry
  exact oppositeLex_of_gadget_common_native_sources
    G K F ψ γ hγ i a b c d hi hplus hminus

/-- In particular the correspondence can be checked at cut 1.
This is the first positive cut, so the previously verified I3
theorem applies without a fictitious cut-zero assertion. -/
theorem oppositeLex_of_gadget_common_native_sources_cut_one
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph)
    (γ : Embedding fiveVertexOrientationGadget G.graph)
    (hγ : γ.TypeRespecting)
    (a b c d : Nat)
    (hplus :
      SameFinitePointedSource G 1
        (ψ a) (ψ b) (γ 2) (γ 3))
    (hminus :
      SameFinitePointedSource G 1
        (ψ c) (ψ d) (γ 3) (γ 4)) :
    DiaryLeafPriority.LexEarlier K
      (stabilisedOrdered G K F (ψ a))
      (stabilisedOrdered G K F (ψ b)) ↔
    ¬ DiaryLeafPriority.LexEarlier K
      (stabilisedOrdered G K F (ψ c))
      (stabilisedOrdered G K F (ψ d)) :=
  oppositeLex_of_gadget_common_native_sources
    G K F ψ γ hγ 1 a b c d (by omega) hplus hminus

end UnorderedEmbedding
end Ordered3Graph
end ThreeUniformDiaries
