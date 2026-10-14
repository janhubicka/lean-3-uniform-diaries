import ThreeUniformDiaries.DiaryTwoSplitNextCut
import ThreeUniformDiaries.DiaryPreembeddingTwoSplit

/-!
# Source witness classes at a diary two-split

Any two leaf pairs whose full pair-type meet is exactly a genuine
two-split i have OPPOSITE incidence bits at i. The V2 coherence
axiom identifies all incident pairs through the successor cut.
The two negative-side pairs from separate witnesses have the
same preceding full type because each agrees up to i with its
positive partner; by the E clause their shared absent edge bit
then identifies their full types through i+1 as well.

This makes the source equivalences needed for target witness
independence a theorem, rather than an additional diary axiom.
The two witnessing comparisons must be aligned so that their
first pairs have the same split-incidence bit. Unaligned pairs
can be handled by exchanging the ordered pair arguments.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {H : Ordered3Graph Nat} (D : RoleDiary H)

/-- A genuine full pair-type meet exactly at i must be witnessed
by opposing incidence bits at i when i has the two-split role.
Otherwise the successor-cut equivalence would contradict
maximality of the capped meet. -/
theorem twoSplit_witness_opposite_incidence (D : RoleDiary H)
    (i a b c d : Nat)
    (hm : IsTwoSplit H i)
    (hia : i < a) (hic : i < c)
    (hmeet : H.twoMeetLevel a b c d = i) :
    ¬ (H.edge i a b ↔ H.edge i c d) := by
  classical
  have hold : H.SameTwoTypeBelow i a b c d := by
    simpa only [hmeet] using H.twoMeetLevel_agree a b c d
  intro hbit
  have hnext : H.SameTwoTypeBelow (i+1) a b c d :=
    (D.sameTwoTypeBelow_succ_iff_of_twoSplit i a b c d hm).2
      ⟨hold, hbit⟩
  have hle : i+1 ≤ H.twoMeetLevel a b c d := by
    apply Nat.le_findGreatest (le_min (by omega) (by omega))
    exact hnext
  omega

/-- Witness-class equality when the FIRST pair of each witnessing
comparison is incident with the split. The second pairs are
necessarily nonincident and already share their preceding types
by transitivity. -/
theorem twoSplit_positive_first_witness_classes (D : RoleDiary H)
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
    (hpos : H.edge i a b) (hpos' : H.edge i a' b') :
    H.SameTwoTypeBelow (i+1) a b a' b' ∧
    H.SameTwoTypeBelow (i+1) c d c' d' := by
  have hPositive : H.SameTwoTypeBelow (i+1) a b a' b' :=
    D.twoSplit_incident_pairTypes_succ i a b a' b' hm
      hab hab' ha hb ha' hb' hpos hpos'
  have hOldPositive : H.SameTwoTypeBelow i a b a' b' :=
    H.sameTwoTypeBelow_mono i (i+1) a b a' b'
      (by omega) hPositive
  have hOldLeft : H.SameTwoTypeBelow i a b c d := by
    simpa only [hmeet] using H.twoMeetLevel_agree a b c d
  have hOldRight : H.SameTwoTypeBelow i a' b' c' d' := by
    simpa only [hmeet'] using H.twoMeetLevel_agree a' b' c' d'
  have hOldNegative : H.SameTwoTypeBelow i c d c' d' :=
    H.sameTwoTypeBelow_trans i c d a b c' d'
      (H.sameTwoTypeBelow_symm i a b c d hOldLeft)
      (H.sameTwoTypeBelow_trans i a b a' b' c' d'
        hOldPositive hOldRight)
  have hOpp := D.twoSplit_witness_opposite_incidence
    i a b c d hm hia hic hmeet
  have hOpp' := D.twoSplit_witness_opposite_incidence
    i a' b' c' d' hm hia' hic' hmeet'
  have hNeg : ¬ H.edge i c d := by
    intro he
    exact hOpp ⟨fun _ => he, fun _ => hpos⟩
  have hNeg' : ¬ H.edge i c' d' := by
    intro he
    exact hOpp' ⟨fun _ => he, fun _ => hpos'⟩
  have hBitNegative : H.edge i c d ↔ H.edge i c' d' :=
    ⟨fun he => False.elim (hNeg he),
     fun he => False.elim (hNeg' he)⟩
  exact ⟨hPositive,
    (D.sameTwoTypeBelow_succ_iff_of_twoSplit i c d c' d' hm).2
      ⟨hOldNegative, hBitNegative⟩⟩

/-- Two witnessing comparisons of the same source two-split have
equal next-cut types in each corresponding pair class whenever
their first pairs have the same incidence bit. This includes the
case where both first pairs are nonincident. -/
theorem twoSplit_aligned_witness_classes (D : RoleDiary H)
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
    (hAligned : H.edge i a b ↔ H.edge i a' b') :
    H.SameTwoTypeBelow (i+1) a b a' b' ∧
    H.SameTwoTypeBelow (i+1) c d c' d' := by
  by_cases hPos : H.edge i a b
  · exact D.twoSplit_positive_first_witness_classes
      i a b c d a' b' c' d' hm
      hia hic hia' hic' hab hcd hab' hcd'
      ha hb hc hd ha' hb' hc' hd'
      hmeet hmeet' hPos (hAligned.mp hPos)
  · have hNeg' : ¬ H.edge i a' b' := by
      intro he
      exact hPos (hAligned.mpr he)
    have hOpp := D.twoSplit_witness_opposite_incidence
      i a b c d hm hia hic hmeet
    have hOpp' := D.twoSplit_witness_opposite_incidence
      i a' b' c' d' hm hia' hic' hmeet'
    have hPosSecond : H.edge i c d := by
      by_contra hNeg
      apply hOpp
      constructor
      · intro h
        exact False.elim (hPos h)
      · intro h
        exact False.elim (hNeg h)
    have hPosSecond' : H.edge i c' d' := by
      by_contra hNeg
      apply hOpp'
      constructor
      · intro h
        exact False.elim (hNeg' h)
      · intro h
        exact False.elim (hNeg h)
    have hMeetSwap : H.twoMeetLevel c d a b = i := by
      rw [H.twoMeetLevel_comm c d a b]
      exact hmeet
    have hMeetSwap' : H.twoMeetLevel c' d' a' b' = i := by
      rw [H.twoMeetLevel_comm c' d' a' b']
      exact hmeet'
    have hResult := D.twoSplit_positive_first_witness_classes
      i c d a b c' d' a' b' hm
      hic hia hic' hia' hcd hab hcd' hab'
      hc hd ha hb hc' hd' ha' hb'
      hMeetSwap hMeetSwap' hPosSecond hPosSecond'
    exact ⟨hResult.2, hResult.1⟩

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
