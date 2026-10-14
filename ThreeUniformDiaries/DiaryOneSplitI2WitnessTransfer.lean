import ThreeUniformDiaries.DiaryOneSplitWitnessClasses
import ThreeUniformDiaries.DiaryPreembeddingOneSplit

/-!
# One-split target meet independence from successor-cut I2

V/E/S identifies both source singleton type classes represented
by arbitrary pairs of leaves witnessing a fixed one-split m.
If an induced target embedding stabilises these source classes
through its image cut φ(m)+1 and the target meet of ONE witness
is at most φ(m), the target meet of EVERY witness agrees.
Oppositely orientated source witnesses are handled by swapping
their two leaves, without assuming that an initially unordered
external hypergraph map preserves the enumeration.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {H K : Ordered3Graph Nat} (D : RoleDiary H)

/-- Full witness independence of the image of a source one-split,
given exactly the target I2 statement and the already checked
placement upper bound. The source witness-class hypotheses of
the earlier local lemma have been discharged by V/E/S. -/
theorem oneSplit_target_witness_independent_of_I2 (D : RoleDiary H)
    (φ : Embedding H K)
    (m u v u' v' : Nat)
    (hm : IsOneSplit H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hu' : IsLeaf H u') (hv' : IsLeaf H v')
    (hmu : m < u) (hmv : m < v)
    (hmu' : m < u') (hmv' : m < v')
    (hmeet : H.oneMeetLevel u v = m)
    (hmeet' : H.oneMeetLevel u' v' = m)
    (hI2 :
      ∀ a b : Nat, m < a → m < b →
        IsLeaf H a → IsLeaf H b →
        H.SameOneTypeBelow (m+1) a b →
        K.SameOneTypeBelow (φ m+1) (φ a) (φ b))
    (hEarly : K.oneMeetLevel (φ u) (φ v) ≤ φ m) :
    K.oneMeetLevel (φ u') (φ v') =
      K.oneMeetLevel (φ u) (φ v) := by
  by_cases hAligned : (H.edge 0 m u ↔ H.edge 0 m u')
  · have hSource := D.oneSplit_aligned_witness_classes
      m u v u' v' hm hu hv hu' hv'
      hmu hmv hmu' hmv' hmeet hmeet' hAligned
    have hTargetU : K.SameOneTypeBelow (φ m+1) (φ u) (φ u') :=
      hI2 u u' hmu hmu' hu hu' hSource.1
    have hTargetV : K.SameOneTypeBelow (φ m+1) (φ v) (φ v') :=
      hI2 v v' hmv hmv' hv hv' hSource.2
    exact K.oneMeetLevel_pairWitness_independent
      (φ m) (φ u) (φ v) (φ u') (φ v')
      (φ.strictMono hmu) (φ.strictMono hmv)
      (φ.strictMono hmu') (φ.strictMono hmv')
      hTargetU hTargetV hEarly
  · have hOpp' : ¬ (H.edge 0 m u' ↔ H.edge 0 m v') :=
      D.oneSplit_witness_opposite_marker
        m u' v' hm hu' hv' hmu' hmv' hmeet'
    have hAlignedSwap : H.edge 0 m u ↔ H.edge 0 m v' := by
      tauto
    have hSwapMeet : H.oneMeetLevel v' u' = m := by
      rw [H.oneMeetLevel_comm v' u']
      exact hmeet'
    have hSource := D.oneSplit_aligned_witness_classes
      m u v v' u' hm hu hv hv' hu'
      hmu hmv hmv' hmu' hmeet hSwapMeet hAlignedSwap
    have hTargetU : K.SameOneTypeBelow (φ m+1) (φ u) (φ v') :=
      hI2 u v' hmu hmv' hu hv' hSource.1
    have hTargetV : K.SameOneTypeBelow (φ m+1) (φ v) (φ u') :=
      hI2 v u' hmv hmu' hv hu' hSource.2
    have hNew :
        K.oneMeetLevel (φ v') (φ u') =
          K.oneMeetLevel (φ u) (φ v) :=
      K.oneMeetLevel_pairWitness_independent
        (φ m) (φ u) (φ v) (φ v') (φ u')
        (φ.strictMono hmu) (φ.strictMono hmv)
        (φ.strictMono hmv') (φ.strictMono hmu')
        hTargetU hTargetV hEarly
    exact (K.oneMeetLevel_comm (φ u') (φ v')).trans hNew

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
