import ThreeUniformDiaries.DiaryFourTailOppositeI3
import ThreeUniformDiaries.DiaryNativeOppositeCalibration
import ThreeUniformDiaries.DiaryFinitePointedEnvelope

/-!
# Actual opposite diary orientation classes have opposite target signs

The two canonical native three-tail pointed sources of an ordered
positive diary leaf pair and an ordered negative pair have already
been proved overlap-compatible. Their four-tail edge amalgam has a
calibration triple. Both compressed sources are genuine finite ATR
codes by the verified role-based pointed-envelope constructor.

The finite shifted-inclusion theorem, the prefix-fixed generic
four-tail embedding, and native I3 therefore force the two original
pair orientations to be opposite after an arbitrary unordered
outer embedding has been fused into an increasing induced map.

In particular, this proof never assumes that the original outer
embedding preserves the enumeration or that an omitted target
level has the same auxiliary type as a source level.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

variable {H : Ordered3Graph Nat}

/-- The actual original positive and negative diary leaf pairs
remain oppositely oriented in the stabilised target image.
All geometric, finite-ATR and calibration hypotheses are
derived from the one role-based diary definition. -/
theorem oppositeLex_native_target_opposite_after_fusion
    (D : RoleDiary H)
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hplus : LexEarlier H a b)
    (hminus : ¬ LexEarlier H c d) :
    LexEarlier K (stabilisedSource G K F ψ a)
      (stabilisedSource G K F ψ b) ↔
    ¬ LexEarlier K (stabilisedSource G K F ψ c)
      (stabilisedSource G K F ψ d) := by
  classical
  let j := ψ 3
  let m := H.oneMeetLevel a b
  let n := H.oneMeetLevel c d
  let fPlus := threeTailInsertion j (ψ m) (ψ a) (ψ b)
  let fMinus := threeTailInsertion j (ψ n) (ψ c) (ψ d)
  let A := G.graph.pullback fPlus
  let B := G.graph.pullback fMinus
  let C := threeTailFreeAmalgam A B j
  have hj : 0 < j := by
    have hh : ψ 0 < ψ 3 := ψ.strictMono (by omega)
    omega
  have ha3 : 3 ≤ a := ha.1
  have hc3 : 3 ≤ c := hc.1
  have hm : IsOneSplit H m :=
    D.singleton_meets a b ha hb (ne_of_lt hab)
  have hn : IsOneSplit H n :=
    D.singleton_meets c d hc hd (ne_of_lt hcd)
  let Eplus : FinitePointedEnvelope G.graph j (ψ a) (ψ b) :=
    FinitePointedEnvelope.ofRoleThreeTail D ψ hψ
      3 a b (by omega) ha3 hab ha hb hm.1
  let Eminus : FinitePointedEnvelope G.graph j (ψ c) (ψ d) :=
    FinitePointedEnvelope.ofRoleThreeTail D ψ hψ
      3 c d (by omega) hc3 hcd hc hd hn.1
  have hfPlus :
      FiniteAuxEmbedding A G.graph fPlus (j+3) := by
    exact Eplus.finite_aux_embedding
  have hfMinus :
      FiniteAuxEmbedding B G.graph fMinus (j+3) := by
    exact Eminus.finite_aux_embedding
  have hfixPlus : ∀ t, t < j → fPlus t = t := by
    intro t ht
    exact threeTailInsertion_fix_prefix
      j (ψ m) (ψ a) (ψ b) t ht
  have hfixMinus : ∀ t, t < j → fMinus t = t := by
    intro t ht
    exact threeTailInsertion_fix_prefix
      j (ψ n) (ψ c) (ψ d) t ht
  have hOverlap : ThreeTailOverlapCompatible A B j :=
    D.oppositeLex_native_threeTail_overlap
      G ψ hψ a b c d hab hcd ha hb hc hd hplus hminus
  have hFirst : fMinus (j+1) = ψ c :=
    threeTailInsertion_first j (ψ n) (ψ c) (ψ d)
  have hSecond : fMinus (j+2) = ψ d :=
    threeTailInsertion_second j (ψ n) (ψ c) (ψ d)
  have hSplit : fMinus j = ψ n :=
    threeTailInsertion_split j (ψ n) (ψ c) (ψ d)
  have hMeetImage :
      G.graph.oneMeetLevel (ψ c) (ψ d) = ψ n :=
    typeRespecting_oneMeetLevel_eq ψ hψ c d
  have hMeetB : B.oneMeetLevel (j+1) (j+2) = j := by
    have hExact :=
      hfMinus.oneMeetLevel_eq (j+1) (j+2) (by omega) (by omega)
    have hMap :
        fMinus (B.oneMeetLevel (j+1) (j+2)) = fMinus j := by
      calc
        fMinus (B.oneMeetLevel (j+1) (j+2)) =
            G.graph.oneMeetLevel (fMinus (j+1)) (fMinus (j+2)) :=
              hExact.symm
        _ = G.graph.oneMeetLevel (ψ c) (ψ d) := by
              rw [hFirst, hSecond]
        _ = ψ n := hMeetImage
        _ = fMinus j := hSplit.symm
    exact hfMinus.strictMono.injective hMap
  let T : OrientationCalibrationTriple C :=
    D.oppositeLex_native_fourTail_has_calibrationTriple
      G ψ hψ a b c d hab hcd ha hb hc hd hplus hminus
  have hCalibration :
      C.oneMeetLevel (j+1) (j+2) = j ∧
      C.SameOneTypeBelow (j+1) (j+1) (j+3) := by
    exact ⟨T.meet_ab, T.same_ac⟩
  have hOpp :=
    oppositeLex_of_fourTail_finiteATR_calibration
      G K F A B j hj fPlus fMinus
      hfPlus hfMinus hfixPlus hfixMinus
      hOverlap hMeetB hCalibration
  change
    LexEarlier K (stabilisedOrdered G K F (ψ a))
      (stabilisedOrdered G K F (ψ b)) ↔
    ¬ LexEarlier K (stabilisedOrdered G K F (ψ c))
      (stabilisedOrdered G K F (ψ d))
  simpa only [fPlus, fMinus,
    threeTailInsertion_first,
    threeTailInsertion_second] using hOpp

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
