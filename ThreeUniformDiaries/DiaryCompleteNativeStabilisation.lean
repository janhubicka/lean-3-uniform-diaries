import ThreeUniformDiaries.DiaryCommonFinitePointedSource
import ThreeUniformDiaries.DiaryFusedSingletonType
import ThreeUniformDiaries.DiaryOrderedStageRecursion

/-!
# The complete native finite-envelope type-stabilisation theorem

The recursively constructed, aux-type-respecting generic selfembedding
simultaneously satisfies all three stabilisation properties:
(I1) its image under an arbitrary INJECTIVE outer map F is increasing;
(I2) equal singleton source types at each positive cut remain equal
     below the prescribed target predecessor-image cut;
(I3) two ordered pairs admitting a SHARED genuine finite ATR pointed
     source retain their full target pair type and lexicographic
     orientation at that same cut.

This is a self-contained, fully quantified theorem about the verified
finite representation of ATR-admissible pointed envelopes. It is the
natural type-theoretic formalisation of the revised stabilisation
lemma. The additional identification of the manuscript's abstract
`Env_G^i(S)=Env_G^i(T)` with `SameFinitePointedSource` is separately
proved for concrete diary two- and three-tail copies and is not
silently assumed here.

The theorem does not cover the cut-zero three-leaf orientation
synchronisation or the final diary pre-embedding, flips and
unavoidability.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- The specifically constructed fused embedding satisfies I1, I2,
and the precise native finite-envelope version of I3 all at once.
The outer F need only be injective. -/
theorem orderedDiaryFusion_complete_native_stabilisation
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F) :
    let g := orderedDiaryFusion G K F hF
    g.AuxTypeRespecting ∧
    StrictMono (fun t => F (g t)) ∧
    (∀ i : Nat, 0 < i →
      ∀ a b : Nat, i ≤ a → i ≤ b →
        G.graph.SameOneTypeBelow i a b →
        K.SameOneTypeBelow
          (F (g (i-1)) + 1)
          (F (g a)) (F (g b))) ∧
    (∀ i a b c d : Nat, 0 < i →
      SameFinitePointedSource G i a b c d →
      K.SameTwoTypeBelow
        (F (g (i-1)) + 1)
        (F (g a)) (F (g b)) (F (g c)) (F (g d)) ∧
      (DiaryLeafPriority.LexEarlier K (F (g a)) (F (g b)) ↔
       DiaryLeafPriority.LexEarlier K (F (g c)) (F (g d)))) := by
  let stages := orderedDiaryEmbeddings G K F hF
  have hs : Embedding.PrefixStable stages :=
    orderedDiaryEmbeddings_prefixStable G K F hF
  have horder : StrictMono
      (fun t => F (orderedDiaryFusion G K F hF t)) := by
    apply Embedding.fusion_order_preserved F stages hs
    intro k u v huv hv
    exact orderedDiaryEmbeddings_increasingPrefix
      G K F hF k u v huv (by omega)
  refine ⟨orderedDiaryFusion_aux G K F hF, horder, ?_, ?_⟩
  · intro i hi a b hia hib htype
    exact orderedDiaryFusion_singletonType_stabilised
      G K F hF i hi a b hia hib htype
  · intro i a b c d hi hcommon
    exact orderedDiaryFusion_I3_of_common_finite_source
      G K F hF i hi a b c d hcommon

/-- Existential type-stabilisation statement in the native finite
pointed-source interface. This is the exact output needed for the
subsequent diary embedding transfer, without requiring a global
enumeration-preserving property from the original outer map. -/
theorem exists_auxEmbedding_complete_native_stabilisation
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F) :
    ∃ g : Embedding G.graph G.graph,
      g.AuxTypeRespecting ∧
      StrictMono (fun t => F (g t)) ∧
      (∀ i : Nat, 0 < i →
        ∀ a b : Nat, i ≤ a → i ≤ b →
          G.graph.SameOneTypeBelow i a b →
          K.SameOneTypeBelow
            (F (g (i-1)) + 1)
            (F (g a)) (F (g b))) ∧
      (∀ i a b c d : Nat, 0 < i →
        SameFinitePointedSource G i a b c d →
        K.SameTwoTypeBelow
          (F (g (i-1)) + 1)
          (F (g a)) (F (g b)) (F (g c)) (F (g d)) ∧
        (DiaryLeafPriority.LexEarlier K (F (g a)) (F (g b)) ↔
         DiaryLeafPriority.LexEarlier K (F (g c)) (F (g d)))) := by
  refine ⟨orderedDiaryFusion G K F hF, ?_⟩
  exact orderedDiaryFusion_complete_native_stabilisation
    G K F hF

end ATRFiniteDecoder
end ThreeUniformDiaries
