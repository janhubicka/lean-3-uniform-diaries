import ThreeUniformDiaries.DiaryPointedFinitePictureEquality
import ThreeUniformDiaries.DiaryFusedEnvelopeColours
import ThreeUniformDiaries.DiaryFiniteATRShapeUniverse

/-!
# The pair-type stabilisation conclusion for diary leaf pairs

The fused generic embedding homogenises actual finite ATR embedding
codes of a common native EnumNode source. For two ordered leaf pairs
of the same full source 2-type, the checked pointed-envelope
comparison shows that their canonical finite EnumNode sources agree
literally. Thus both canonical inclusions become codes of ONE source
shape in the finite source universe.

This proves the concrete pair-type and lexicographic orientation
part of the lower-bound stabilisation lemma for diary pairs in the
two-tail case. The three-tail branch is handled separately, using
the corrected V/E/S diary marker laws. No arbitrary mixed-pair
aux-meet preservation or invented global zero-tail embedding occurs.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- For a type-respecting image of a source full-2-type pair whose
singleton meet is before the cut, the two canonical two-tail
pointed envelopes represent a SINGLE genuine finite ATR source.

Under the fused stabilisation embedding, the target pairs have
equal full 2-types and equal lexicographic orientation at the
exact predecessor target cut. The outer map F is only injective. -/
theorem orderedDiaryFusion_twoTail_pairType_orientation
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i a b c d : Nat) (hi : 0 < i)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d)
    (hpair : H.SameTwoTypeBelow i a b c d)
    (hearly : H.oneMeetLevel a b < i) :
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
    have h := ψ.strictMono hi
    dsimp [j]
    omega
  have hbI : i ≤ b := hia.trans hab.le
  have hdI : i ≤ d := hic.trans hcd.le
  have hearlyCD : H.oneMeetLevel c d < i :=
    (H.sameTwoTypeBelow_same_envelope_case
      i a b c d hia hbI hic hdI hpair).mp hearly
  let E₀ : FinitePointedEnvelope G.graph j (ψ a) (ψ b) :=
    FinitePointedEnvelope.ofTwoTail ψ hψ i a b
      hearly hia hab
  let E₁ : FinitePointedEnvelope G.graph j (ψ c) (ψ d) :=
    FinitePointedEnvelope.ofTwoTail ψ hψ i c d
      hearlyCD hic hcd
  have hsource : E₀.finiteEnum = E₁.finiteEnum := by
    change
      ((G.graph.pullback
        (twoTailInsertion j (ψ a) (ψ b))).initialSegment (j+2)) =
      ((G.graph.pullback
        (twoTailInsertion j (ψ c) (ψ d))).initialSegment (j+2))
    exact Ordered3Graph.two_tail_finiteEnum_eq_of_sameTwoType
      ψ hψ i a b c d hia hic hab hcd hpair
  let A : ProtectedSource j := twoVertexSource j E₀.finiteEnum
  have hA : A ∈ smallSourceUniverse j :=
    twoVertexSource_mem j E₀.finiteEnum
  let e₀ : A.Code G := E₀.finiteATRCode
  have hf : FiniteAuxEmbedding E₀.finiteEnum.toOrdered3Graph
      G.graph E₁.enumerate (j+2) := by
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
    change E₀.enumerate j = ψ a
    exact twoTailInsertion_first j (ψ a) (ψ b)
  have hl₀ : e₀.image A.lastIndex = ψ b := by
    change E₀.enumerate (j+1) = ψ b
    exact twoTailInsertion_second j (ψ a) (ψ b)
  have hp₁ : e₁.image A.penultimateIndex = ψ c := by
    change E₁.enumerate j = ψ c
    exact twoTailInsertion_first j (ψ c) (ψ d)
  have hl₁ : e₁.image A.lastIndex = ψ d := by
    change E₁.enumerate (j+1) = ψ d
    exact twoTailInsertion_second j (ψ c) (ψ d)
  have htype := orderedDiaryFusion_pairType_orientation
    G K F hF j hj A hA e₀ e₁ he₀ he₁
  simpa only [hp₀, hl₀, hp₁, hl₁] using htype

end ATRFiniteDecoder
end ThreeUniformDiaries
