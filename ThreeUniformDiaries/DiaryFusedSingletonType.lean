import ThreeUniformDiaries.DiaryFusedEnvelopeColours
import ThreeUniformDiaries.DiaryFiniteSingletonATR

/-!
# Singleton-type stabilisation in the fused lower-bound embedding

Two source vertices a,b beyond the protected cut i with the same
1-type below i determine literally identical native finite
singleton-envelope EnumNode sources. Their canonical inclusions
are therefore genuine finite ATR embeddings of ONE source, with
the entire prefix fixed.

The verified fusion-colour theorem applies to these two codes,
and its last-coordinate singleton component yields exactly the
target 1-type agreement at
    F(g(i-1)) + 1,
where g is the recursively constructed aux-type-respecting
generic self-embedding and F is an ARBITRARY INJECTIVE outer map.

This closes the singleton-type conclusion (I2) in the manuscript's
generic-hypergraph interface, without assuming that F is ordered.
The pointed-pair conclusion (I3) uses the companion finite-code
pair-type/orientation result and still needs the concrete diary
envelope-to-code correspondence.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Condition (I2) of the type-stabilisation lemma: equal source
singleton types over a positive cut remain equal in the
arbitrary target below the outer image of the fused predecessor,
plus one. The same g simultaneously satisfies (I1). -/
theorem orderedDiaryFusion_singletonType_stabilised
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (i : Nat) (hi : 0 < i)
    (a b : Nat) (hia : i ≤ a) (hib : i ≤ b)
    (htype : G.graph.SameOneTypeBelow i a b) :
    K.SameOneTypeBelow
      (F (orderedDiaryFusion G K F hF (i-1)) + 1)
      (F (orderedDiaryFusion G K F hF a))
      (F (orderedDiaryFusion G K F hF b)) := by
  let E₀ : FiniteSingletonEnvelope G.graph i a :=
    FiniteSingletonEnvelope.ofVertex G.graph i a hia
  let E₁ : FiniteSingletonEnvelope G.graph i b :=
    FiniteSingletonEnvelope.ofVertex G.graph i b hib
  have hEnum : E₀.finiteEnum = E₁.finiteEnum :=
    E₀.finiteEnum_eq_of_sameOneType E₁ htype
  let A : ProtectedSource i := oneVertexSource i E₀.finiteEnum
  have hA : A ∈ smallSourceUniverse i :=
    oneVertexSource_mem i E₀.finiteEnum
  let e₀ : A.Code G := E₀.finiteATRCode
  have hf : FiniteAuxEmbedding
      E₀.finiteEnum.toOrdered3Graph G.graph E₁.enumerate (i+1) := by
    rw [hEnum]
    exact E₁.finite_aux_embedding.of_initialSegment
  let e₁ : A.Code G :=
    FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding E₁.enumerate hf
  have he₀ : A.FixesPrefix G e₀ := by
    intro j hj
    exact E₀.finiteATRCode_fix_prefix j hj
  have he₁ : A.FixesPrefix G e₁ := by
    intro j hj
    change E₁.enumerate j.val = j.val
    exact E₁.protected_prefix j.val hj
  have hlast₀ : e₀.image A.lastIndex = a := by
    change E₀.finiteATRCode.image (Fin.last i) = a
    exact E₀.finiteATRCode_last
  have hlast₁ : e₁.image A.lastIndex = b := by
    change E₁.enumerate i = b
    exact E₁.endpoint
  have hPair := orderedDiaryFusion_pairType_orientation
    G K F hF i hi A hA e₀ e₁ he₀ he₁
  have hOne := hPair.1.2.1
  simpa only [hlast₀, hlast₁] using hOne

end ATRFiniteDecoder
end ThreeUniformDiaries
