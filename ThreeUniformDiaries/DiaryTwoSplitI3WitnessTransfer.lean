import ThreeUniformDiaries.DiaryTwoSplitWitnessClasses

/-!
# Two-split witness independence from successor-cut I3

The diary V/E/S axioms already identify the source types of
all equivalent witnesses for a fixed two-split, with swapping
of the two ordered pair arguments when their incidence classes
are oppositely oriented.

This theorem is the abstract final local step: an induced ordered
target embedding which stabilises equal source leaf-pair types at
cut i+1 and places ONE witness meet by image(i) must send EVERY
witness of that 2-split to the same target full pair-type meet.

No type-preservation across skipped target levels is assumed.
The actual fused I3 map and the placement estimate supply the
two explicit target hypotheses in the separate application.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {H K : Ordered3Graph Nat} (D : RoleDiary H)

/-- Any two witnesses of a fixed source two-split determine the
same target full type meet, provided full leaf-pair I3 holds at
the successor target cut and the first witness's target meet
occurs by the image of the split. There is NO additional source
witness-class assumption. -/
theorem twoSplit_target_witness_independent_of_I3 (D : RoleDiary H)
    (φ : Embedding H K)
    (i a b c d a' b' c' d' : Nat)
    (hm : IsTwoSplit H i)
    (hia : i < a) (hic : i < c)
    (hia' : i < a') (hic' : i < c')
    (hab : a < b) (hcd : c < d)
    (hab' : a' < b') (hcd' : c' < d')
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (ha' : IsLeaf H a') (hb' : IsLeaf H b')
    (hc' : IsLeaf H c') (hd' : IsLeaf H d')
    (hmeet : H.twoMeetLevel a b c d = i)
    (hmeet' : H.twoMeetLevel a' b' c' d' = i)
    (hI3 :
      ∀ u v w z : Nat,
        i < u → u < v → i < w → w < z →
        IsLeaf H u → IsLeaf H v → IsLeaf H w → IsLeaf H z →
        H.SameTwoTypeBelow (i+1) u v w z →
        K.SameTwoTypeBelow (φ i+1) (φ u) (φ v) (φ w) (φ z))
    (hEarly :
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) ≤ φ i) :
    K.twoMeetLevel (φ a') (φ b') (φ c') (φ d') =
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) := by
  by_cases hAligned : (H.edge i a b ↔ H.edge i a' b')
  · have hSource := D.twoSplit_aligned_witness_classes
      i a b c d a' b' c' d' hm
      hia hic hia' hic' hab hcd hab' hcd'
      ha hb hc hd ha' hb' hc' hd'
      hmeet hmeet' hAligned
    have hTargetA : K.SameTwoTypeBelow (φ i+1)
        (φ a) (φ b) (φ a') (φ b') :=
      hI3 a b a' b' hia hab hia' hab' ha hb ha' hb' hSource.1
    have hTargetB : K.SameTwoTypeBelow (φ i+1)
        (φ c) (φ d) (φ c') (φ d') :=
      hI3 c d c' d' hic hcd hic' hcd' hc hd hc' hd' hSource.2
    exact K.twoMeetLevel_pairWitness_independent
      (φ i) (φ a) (φ b) (φ c) (φ d)
      (φ a') (φ b') (φ c') (φ d')
      (φ.strictMono hia) (φ.strictMono hic)
      (φ.strictMono hia') (φ.strictMono hic')
      hTargetA hTargetB hEarly
  · have hOpposite' : ¬ (H.edge i a' b' ↔ H.edge i c' d') :=
      D.twoSplit_witness_opposite_incidence
        i a' b' c' d' hm hia' hic' hmeet'
    have hAlignedSwap : H.edge i a b ↔ H.edge i c' d' := by
      tauto
    have hMeetSwap : H.twoMeetLevel c' d' a' b' = i := by
      rw [H.twoMeetLevel_comm c' d' a' b']
      exact hmeet'
    have hSource := D.twoSplit_aligned_witness_classes
      i a b c d c' d' a' b' hm
      hia hic hic' hia' hab hcd hcd' hab'
      ha hb hc hd hc' hd' ha' hb'
      hmeet hMeetSwap hAlignedSwap
    have hTargetA : K.SameTwoTypeBelow (φ i+1)
        (φ a) (φ b) (φ c') (φ d') :=
      hI3 a b c' d' hia hab hic' hcd' ha hb hc' hd' hSource.1
    have hTargetB : K.SameTwoTypeBelow (φ i+1)
        (φ c) (φ d) (φ a') (φ b') :=
      hI3 c d a' b' hic hcd hia' hab' hc hd ha' hb' hSource.2
    have hSwapTarget :
        K.twoMeetLevel (φ c') (φ d') (φ a') (φ b') =
          K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) :=
      K.twoMeetLevel_pairWitness_independent
        (φ i) (φ a) (φ b) (φ c) (φ d)
        (φ c') (φ d') (φ a') (φ b')
        (φ.strictMono hia) (φ.strictMono hic)
        (φ.strictMono hic') (φ.strictMono hia')
        hTargetA hTargetB hEarly
    exact (K.twoMeetLevel_comm (φ a') (φ b') (φ c') (φ d')).trans
      hSwapTarget

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
