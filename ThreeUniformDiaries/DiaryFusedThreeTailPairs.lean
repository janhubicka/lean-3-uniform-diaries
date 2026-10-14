import ThreeUniformDiaries.DiaryFusedTwoTailPairs
import ThreeUniformDiaries.DiaryRoleEnvelopeAssembly

/-!
# Fused 2-type and orientation stabilisation for three-tail diary pairs

The three-tail envelope case is the difficult branch of the diary
lower-bound proof. The one-split vertex is at or above the protected
source cut, so the actual finite envelope has three exterior
vertices. Its corrected V/E/S marker laws ensure that same-full-
2-type ordered leaf pairs induce IDENTICAL three-tail native
EnumNode sources even with gaps in the ambient generic enumeration.

Consequently the two canonical finite ATR inclusions are codes of
the SAME source. The already verified fusion-colour theorem therefore
equates both target singleton coordinates, their full auxiliary pair
type, and their lexicographic orientation at the correct predecessor
outer target cut. This proves the concrete three-tail I3 transfer
for a type-respecting image of a complete role-based diary.

The external injection is not assumed increasing. We do not use
global mixed-pair auxiliary meet preservation or a fictitious
infinite-zero-tail embedding.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Same-full-2-type ordered diary leaf pairs with their split at
or after the protected source cut have equal complete 2-types and
lexicographic orientation after the fused lower-bound embedding.

The source diary axioms are exactly the checked V/E/S role laws;
the ambient map into the generic graph is genuinely
type-respecting and may skip arbitrary enumeration levels. -/
theorem orderedDiaryFusion_threeTail_leafPairType_orientation
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    {H : Ordered3Graph Nat}
    (D : DiaryLeafPriority.RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i a b c d : Nat) (hi : 3 ≤ i)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d)
    (ha : DiaryLeafPriority.IsLeaf H a)
    (hb : DiaryLeafPriority.IsLeaf H b)
    (hc : DiaryLeafPriority.IsLeaf H c)
    (hd : DiaryLeafPriority.IsLeaf H d)
    (hpair : H.SameTwoTypeBelow i a b c d)
    (hcase : i ≤ H.oneMeetLevel a b) :
    let g := orderedDiaryFusion G K F hF
    let j := ψ i
    let N := F (g (j-1)) + 1
    K.SameTwoTypeBelow N
      (F (g (ψ a))) (F (g (ψ b)))
      (F (g (ψ c))) (F (g (ψ d))) ∧
    (DiaryLeafPriority.LexEarlier K
        (F (g (ψ a))) (F (g (ψ b))) ↔
      DiaryLeafPriority.LexEarlier K
        (F (g (ψ c))) (F (g (ψ d)))) := by
  let j := ψ i
  have hj : 0 < j := by
    have h0i : 0 < i := by omega
    have hh := ψ.strictMono h0i
    dsimp [j]
    omega
  have hbI : i ≤ b := hia.trans hab.le
  have hdI : i ≤ d := hic.trans hcd.le
  have hsameCase := H.sameTwoTypeBelow_same_envelope_case
    i a b c d hia hbI hic hdI hpair
  have hcaseCD : i ≤ H.oneMeetLevel c d := by
    by_contra hnot
    have hlt : H.oneMeetLevel c d < i := Nat.lt_of_not_ge hnot
    have hearly := hsameCase.mpr hlt
    omega
  let E₀ : FinitePointedEnvelope G.graph j (ψ a) (ψ b) :=
    FinitePointedEnvelope.ofRoleThreeTail
      D ψ hψ i a b hi hia hab ha hb hcase
  let E₁ : FinitePointedEnvelope G.graph j (ψ c) (ψ d) :=
    FinitePointedEnvelope.ofRoleThreeTail
      D ψ hψ i c d hi hic hcd hc hd hcaseCD
  have hsource : E₀.finiteEnum = E₁.finiteEnum := by
    change
      ((G.graph.pullback
        (threeTailInsertion j (ψ (H.oneMeetLevel a b))
          (ψ a) (ψ b))).initialSegment (j+3)) =
      ((G.graph.pullback
        (threeTailInsertion j (ψ (H.oneMeetLevel c d))
          (ψ c) (ψ d))).initialSegment (j+3))
    exact D.three_tail_finiteEnum_eq_of_same_leaf_twoType
      ψ hψ i a b c d hi hia hic hab hcd
      ha hb hc hd hpair hcase
  let A : ProtectedSource j := threeVertexSource j E₀.finiteEnum
  have hA : A ∈ smallSourceUniverse j :=
    threeVertexSource_mem j E₀.finiteEnum
  let e₀ : A.Code G := E₀.finiteATRCode
  have hf : FiniteAuxEmbedding E₀.finiteEnum.toOrdered3Graph
      G.graph E₁.enumerate (j+3) := by
    rw [hsource]
    exact E₁.finite_aux_embedding.of_initialSegment
  let e₁ : A.Code G :=
    FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding E₁.enumerate hf
  have he₀ : A.FixesPrefix G e₀ := by
    intro t ht
    exact E₀.finiteATRCode_fix_prefix t ht
  have he₁ : A.FixesPrefix G e₁ := by
    intro t ht
    change E₁.enumerate t.val = t.val
    exact E₁.protected_prefix t.val ht
  have hp₀ : e₀.image A.penultimateIndex = ψ a := by
    change E₀.enumerate (j+1) = ψ a
    exact threeTailInsertion_first j
      (ψ (H.oneMeetLevel a b)) (ψ a) (ψ b)
  have hl₀ : e₀.image A.lastIndex = ψ b := by
    change E₀.enumerate (j+2) = ψ b
    exact threeTailInsertion_second j
      (ψ (H.oneMeetLevel a b)) (ψ a) (ψ b)
  have hp₁ : e₁.image A.penultimateIndex = ψ c := by
    change E₁.enumerate (j+1) = ψ c
    exact threeTailInsertion_first j
      (ψ (H.oneMeetLevel c d)) (ψ c) (ψ d)
  have hl₁ : e₁.image A.lastIndex = ψ d := by
    change E₁.enumerate (j+2) = ψ d
    exact threeTailInsertion_second j
      (ψ (H.oneMeetLevel c d)) (ψ c) (ψ d)
  have htype := orderedDiaryFusion_pairType_orientation
    G K F hF j hj A hA e₀ e₁ he₀ he₁
  simpa only [hp₀, hl₀, hp₁, hl₁] using htype

end ATRFiniteDecoder
end ThreeUniformDiaries
