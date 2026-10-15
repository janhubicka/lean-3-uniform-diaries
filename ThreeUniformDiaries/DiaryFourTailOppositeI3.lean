import ThreeUniformDiaries.DiaryFourTailCommonFiniteCodes
import ThreeUniformDiaries.DiaryFourTailGenericRealization
import ThreeUniformDiaries.DiaryOrientationCalibrationTriple

/-!
# Opposite orientation transported from a four-tail calibration

Suppose two native three-tail finite ATR sources share a prefix
and have compatible induced edge profiles. Their ordered four-tail
free amalgam is an induced source in which the first inclusion is
literal and the second shifts the last two vertices by one.
The shifted finite ATR inclusion is verified separately, under
the genuinely necessary split distinction.

An auxiliary-type-respecting fixed-prefix generic embedding of the
four-tail source transports BOTH finite ATR codes to the generic
hypergraph. I3, applied independently to each source, identifies
the two original target orientations with the two adjacent
calibration-pair target orientations. The verified three-leaf
orientation pivot makes the latter opposite.

No global auxiliary meet preservation by the shift, no cut-zero I3,
and no assumption that the outer unordered embedding is increasing.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace UnorderedEmbedding

open ATRFiniteDecoder

/-- Entire opposite-target orientation comparison supplied by the
four-tail calibration and two genuine finite three-tail ATR codes.
The hypotheses are local and entirely finite except for the
existing generic and stabilised embeddings. -/
theorem oppositeLex_of_fourTail_finiteATR_calibration
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (A B : Ordered3Graph Nat) (j : Nat) (hj : 0 < j)
    (fA fB : Nat → Nat)
    (hfA : FiniteAuxEmbedding A G.graph fA (j+3))
    (hfB : FiniteAuxEmbedding B G.graph fB (j+3))
    (hfixA : ∀ t, t < j → fA t = t)
    (hfixB : ∀ t, t < j → fB t = t)
    (hOverlap : ThreeTailOverlapCompatible A B j)
    (hMeetB : B.oneMeetLevel (j+1) (j+2) = j)
    (hCalibration :
      (threeTailFreeAmalgam A B j).oneMeetLevel
        (j+1) (j+2) = j ∧
      (threeTailFreeAmalgam A B j).SameOneTypeBelow
        (j+1) (j+1) (j+3)) :
    let Φ := stabilisedOrdered G K F
    DiaryLeafPriority.LexEarlier K
      (Φ (fA (j+1))) (Φ (fA (j+2))) ↔
    ¬ DiaryLeafPriority.LexEarlier K
      (Φ (fB (j+1))) (Φ (fB (j+2))) := by
  let C := threeTailFreeAmalgam A B j
  let Φ := stabilisedOrdered G K F
  have hPrefix : C.initialSegment j = G.graph.initialSegment j := by
    apply initialSegment_eq_of_prefix_edge_agreement C G.graph j
    intro x y z hxy hyz hz
    have hx : x < j := by omega
    have hy : y < j := by omega
    have hC : C.edge x y z ↔ A.edge x y z :=
      threeTailFreeAmalgam_left A B j x y z (by omega)
    have hA : A.edge x y z ↔
        G.graph.edge (fA x) (fA y) (fA z) :=
      hfA.edge_iff x y z hxy hyz (by omega)
    simpa only [hfixA x hx, hfixA y hy, hfixA z hz] using
      hC.trans hA
  obtain ⟨χ, hχ, hfixχ⟩ :=
    exists_auxTypeRespecting_embedding_fix_prefix G C j hj hPrefix
  have hleftFinite :
      FiniteAuxEmbedding A G.graph (fun t => χ t) (j+3) := by
    exact (threeTailFreeAmalgam_left_finiteAuxEmbedding
      A B j).postcompose χ hχ
  have hrightFinite :
      FiniteAuxEmbedding B G.graph
        (fun t => χ (threeTailShift j t)) (j+3) := by
    exact (threeTailFreeAmalgam_right_finiteAuxEmbedding_of_meet
      A B j hOverlap hMeetB).postcompose χ hχ
  have hfixRight : ∀ t, t < j →
      χ (threeTailShift j t) = t := by
    intro t ht
    rw [threeTailShift_prefix j t (by omega)]
    exact hfixχ t ht
  have hCommonLeft :
      SameFinitePointedSource G j
        (fA (j+1)) (fA (j+2))
        (χ (j+1)) (χ (j+2)) :=
    sameFinitePointedSource_of_threeTail_finiteAuxEmbeddings
      G A j fA (fun t => χ t) hfA hleftFinite
      hfixA hfixχ
  have hCommonRight :
      SameFinitePointedSource G j
        (fB (j+1)) (fB (j+2))
        (χ (j+2)) (χ (j+3)) := by
    have hh :=
      sameFinitePointedSource_of_threeTail_finiteAuxEmbeddings
        G B j fB (fun t => χ (threeTailShift j t))
        hfB hrightFinite hfixB hfixRight
    simpa only [threeTailShift_firstLeaf,
      threeTailShift_secondLeaf] using hh
  have hI3Left :
      DiaryLeafPriority.LexEarlier K
        (Φ (fA (j+1))) (Φ (fA (j+2))) ↔
      DiaryLeafPriority.LexEarlier K
        (Φ (χ (j+1))) (Φ (χ (j+2))) :=
    (stabilisedOrdered_pointedPairTypes
      G K F j (fA (j+1)) (fA (j+2))
        (χ (j+1)) (χ (j+2)) hj hCommonLeft).2
  have hI3Right :
      DiaryLeafPriority.LexEarlier K
        (Φ (fB (j+1))) (Φ (fB (j+2))) ↔
      DiaryLeafPriority.LexEarlier K
        (Φ (χ (j+2))) (Φ (χ (j+3))) :=
    (stabilisedOrdered_pointedPairTypes
      G K F j (fB (j+1)) (fB (j+2))
        (χ (j+2)) (χ (j+3)) hj hCommonRight).2
  let T : OrientationCalibrationTriple C := {
    m := j
    a := j+1
    b := j+2
    c := j+3
    m_lt_a := by omega
    a_lt_b := by omega
    b_lt_c := by omega
    meet_ab := hCalibration.1
    same_ac := hCalibration.2
  }
  have hOpp :
      DiaryLeafPriority.LexEarlier K
        (Φ (χ (j+1))) (Φ (χ (j+2))) ↔
      ¬ DiaryLeafPriority.LexEarlier K
        (Φ (χ (j+2))) (Φ (χ (j+3))) := by
    exact (T.source_and_stabilised_target_opposite
      G K F χ hχ.typeRespecting).2
  exact hI3Left.trans (hOpp.trans (not_congr hI3Right.symm))

end UnorderedEmbedding
end Ordered3Graph
end ThreeUniformDiaries
