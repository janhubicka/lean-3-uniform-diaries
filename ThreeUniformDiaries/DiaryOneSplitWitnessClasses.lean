import ThreeUniformDiaries.DiaryOneSplitNextCut
import ThreeUniformDiaries.DiaryPreembeddingOneSplit

/-!
# Witness classes for genuine diary one-splits

The one-split analogue of the two-split witness calculation.
The singleton type of a leaf through a one-split m gains only
the edge(0,m,leaf) bit. Positive witnesses are coherent by V1,
while negative witnesses agree below m by comparison with their
positive counterparts; equality of their absent marker bits
upgrades this to cut m+1.

Thus two comparisons with the same genuine singleton meet m
have the same two successor-cut source classes after aligning
their positive/negative orientations. No additional one-split
coherence requirement is postulated.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {H : Ordered3Graph Nat} (D : RoleDiary H)

/-- Equality of singleton types at a fixed cut is symmetric. -/
private theorem oneType_symm (l u v : Nat)
    (h : H.SameOneTypeBelow l u v) :
    H.SameOneTypeBelow l v u := by
  intro x y hxy hy
  exact (h hxy hy).symm

/-- Equality of singleton types at a fixed cut is transitive. -/
private theorem oneType_trans (l u v w : Nat)
    (h₁ : H.SameOneTypeBelow l u v)
    (h₂ : H.SameOneTypeBelow l v w) :
    H.SameOneTypeBelow l u w := by
  intro x y hxy hy
  exact (h₁ hxy hy).trans (h₂ hxy hy)

/-- Equality of singleton types restricts to a smaller cut. -/
private theorem oneType_mono (l l' u v : Nat) (hll : l ≤ l')
    (h : H.SameOneTypeBelow l' u v) :
    H.SameOneTypeBelow l u v := by
  intro x y hxy hy
  exact h hxy (lt_of_lt_of_le hy hll)

/-- Positive first singleton witnesses for the SAME genuine
one-split m have matching successor-cut types on both sides
of their splitting comparisons. -/
theorem oneSplit_positive_first_witness_classes
    (m u v u' v' : Nat)
    (hm : IsOneSplit H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hu' : IsLeaf H u') (hv' : IsLeaf H v')
    (hmu : m < u) (hmv : m < v)
    (hmu' : m < u') (hmv' : m < v')
    (hmeet : H.oneMeetLevel u v = m)
    (hmeet' : H.oneMeetLevel u' v' = m)
    (hpos : H.edge 0 m u) (hpos' : H.edge 0 m u') :
    H.SameOneTypeBelow (m+1) u u' ∧
    H.SameOneTypeBelow (m+1) v v' := by
  have hPositive : H.SameOneTypeBelow (m+1) u u' :=
    D.oneSplit_incident_oneTypes_succ m u u' hm hu hu' hpos hpos'
  have hAtM : H.SameOneTypeBelow m u u' :=
    oneType_mono m (m+1) u u' (by omega) hPositive
  have hOld : H.SameOneTypeBelow m u v := by
    simpa only [hmeet] using H.oneMeetLevel_agree u v
  have hOld' : H.SameOneTypeBelow m u' v' := by
    simpa only [hmeet'] using H.oneMeetLevel_agree u' v'
  have hNegativeBelow : H.SameOneTypeBelow m v v' :=
    oneType_trans m v u v'
      (oneType_symm m u v hOld)
      (oneType_trans m u u' v' hAtM hOld')
  have hOpp : ¬ (H.edge 0 m u ↔ H.edge 0 m v) :=
    D.oneSplit_witness_opposite_marker m u v hm hu hv
      hmu hmv hmeet
  have hOpp' : ¬ (H.edge 0 m u' ↔ H.edge 0 m v') :=
    D.oneSplit_witness_opposite_marker m u' v' hm hu' hv'
      hmu' hmv' hmeet'
  have hNoV : ¬ H.edge 0 m v := by
    intro hev
    exact hOpp ⟨fun _ => hev, fun _ => hpos⟩
  have hNoV' : ¬ H.edge 0 m v' := by
    intro hev
    exact hOpp' ⟨fun _ => hev, fun _ => hpos'⟩
  have hBit : H.edge 0 m v ↔ H.edge 0 m v' :=
    ⟨fun h => False.elim (hNoV h),
     fun h => False.elim (hNoV' h)⟩
  have hNegative : H.SameOneTypeBelow (m+1) v v' :=
    (D.sameOneTypeBelow_succ_iff_of_oneSplit m v v' hm hv hv').2
      ⟨hNegativeBelow, hBit⟩
  exact ⟨hPositive, hNegative⟩

/-- The successor-cut witness classes are independent of the
representatives even when both FIRST leaves are on the
negative side; swap both comparisons and use singleton meet
symmetry. -/
theorem oneSplit_aligned_witness_classes
    (m u v u' v' : Nat)
    (hm : IsOneSplit H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hu' : IsLeaf H u') (hv' : IsLeaf H v')
    (hmu : m < u) (hmv : m < v)
    (hmu' : m < u') (hmv' : m < v')
    (hmeet : H.oneMeetLevel u v = m)
    (hmeet' : H.oneMeetLevel u' v' = m)
    (haligned : H.edge 0 m u ↔ H.edge 0 m u') :
    H.SameOneTypeBelow (m+1) u u' ∧
    H.SameOneTypeBelow (m+1) v v' := by
  by_cases hpos : H.edge 0 m u
  · exact D.oneSplit_positive_first_witness_classes
      m u v u' v' hm hu hv hu' hv'
      hmu hmv hmu' hmv' hmeet hmeet' hpos (haligned.mp hpos)
  · have hno : ¬ H.edge 0 m u' := by
      intro he
      exact hpos (haligned.mpr he)
    have hOpp := D.oneSplit_witness_opposite_marker
      m u v hm hu hv hmu hmv hmeet
    have hOpp' := D.oneSplit_witness_opposite_marker
      m u' v' hm hu' hv' hmu' hmv' hmeet'
    have hposV : H.edge 0 m v := by
      by_contra hnoV
      apply hOpp
      constructor
      · intro h
        exact False.elim (hpos h)
      · intro h
        exact False.elim (hnoV h)
    have hposV' : H.edge 0 m v' := by
      by_contra hnoV'
      apply hOpp'
      constructor
      · intro h
        exact False.elim (hno h)
      · intro h
        exact False.elim (hnoV' h)
    have hmeetSwap : H.oneMeetLevel v u = m := by
      rw [H.oneMeetLevel_comm v u]
      exact hmeet
    have hmeetSwap' : H.oneMeetLevel v' u' = m := by
      rw [H.oneMeetLevel_comm v' u']
      exact hmeet'
    have hResult := D.oneSplit_positive_first_witness_classes
      m v u v' u' hm hv hu hv' hu'
      hmv hmu hmv' hmu' hmeetSwap hmeetSwap' hposV hposV'
    exact ⟨hResult.2, hResult.1⟩

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
