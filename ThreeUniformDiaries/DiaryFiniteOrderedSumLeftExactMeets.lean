import ThreeUniformDiaries.DiaryFiniteOrderedSumLeftTypeTransport
import ThreeUniformDiaries.DiaryFiniteOrderedSumRoles

/-!
# Exact meets and split witnesses inside the left finite block

The finite ordered sum contains the whole original left finite
block as an induced initial segment. All singleton and auxiliary
type comparisons on left vertices are unchanged, at every cut
(including cuts beyond the left length).

Consequently the *numerical* capped singleton and full ordered-pair
meets of original left vertices are identical to their source
values, with no V/E/S assumptions. Every source split witness whose
leaves lie in the finite frame is then an exact target witness.

This module records only left-block facts. The finite right-block
witness transfer uses separate strict meet calculations.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- The original left initial segment preserves *all* capped
singleton meet levels numerically, even in the absence of S1. -/
theorem finiteTwoBlockCarrier_left_oneMeet_exact
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (a b : Nat) (han : a < n) (hbn : b < n) :
    (finiteTwoBlockCarrier H K n m bits).oneMeetLevel a b =
      H.oneMeetLevel a b := by
  classical
  let G := finiteTwoBlockCarrier H K n m bits
  have hAtTarget : G.SameOneTypeBelow (G.oneMeetLevel a b) a b :=
    G.oneMeetLevel_agree a b
  have hAtSource : H.SameOneTypeBelow (H.oneMeetLevel a b) a b :=
    H.oneMeetLevel_agree a b
  have hTransportTarget : H.SameOneTypeBelow
      (G.oneMeetLevel a b) a b :=
    (finiteTwoBlockCarrier_left_oneType_iff
      FH FK bits (G.oneMeetLevel a b) a b han hbn).mp hAtTarget
  have hTransportSource : G.SameOneTypeBelow
      (H.oneMeetLevel a b) a b :=
    (finiteTwoBlockCarrier_left_oneType_iff
      FH FK bits (H.oneMeetLevel a b) a b han hbn).mpr hAtSource
  have hGT : G.oneMeetLevel a b ≤ H.oneMeetLevel a b :=
    Nat.le_findGreatest (G.oneMeetLevel_le_min a b)
      hTransportTarget
  have hTG : H.oneMeetLevel a b ≤ G.oneMeetLevel a b :=
    Nat.le_findGreatest (H.oneMeetLevel_le_min a b)
      hTransportSource
  change G.oneMeetLevel a b = H.oneMeetLevel a b
  omega

/-- Full ordered-pair meet levels are also *numerically identical*
in the initial left block, for arbitrary left vertices. -/
theorem finiteTwoBlockCarrier_left_twoMeet_exact
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (bits : Nat → Bool)
    (a b c d : Nat)
    (han : a < n) (hbn : b < n)
    (hcn : c < n) (hdn : d < n) :
    (finiteTwoBlockCarrier H K n m bits).twoMeetLevel a b c d =
      H.twoMeetLevel a b c d := by
  classical
  let G := finiteTwoBlockCarrier H K n m bits
  have hAtTarget : G.SameTwoTypeBelow
      (G.twoMeetLevel a b c d) a b c d :=
    G.twoMeetLevel_agree a b c d
  have hAtSource : H.SameTwoTypeBelow
      (H.twoMeetLevel a b c d) a b c d :=
    H.twoMeetLevel_agree a b c d
  have hTransportTarget : H.SameTwoTypeBelow
      (G.twoMeetLevel a b c d) a b c d :=
    (finiteTwoBlockCarrier_left_twoType_iff FH FK bits
      (G.twoMeetLevel a b c d) a b c d
      han hbn hcn hdn).mp hAtTarget
  have hTransportSource : G.SameTwoTypeBelow
      (H.twoMeetLevel a b c d) a b c d :=
    (finiteTwoBlockCarrier_left_twoType_iff FH FK bits
      (H.twoMeetLevel a b c d) a b c d
      han hbn hcn hdn).mpr hAtSource
  have hGT : G.twoMeetLevel a b c d ≤ H.twoMeetLevel a b c d :=
    Nat.le_findGreatest (G.twoMeetLevel_le_min a b c d)
      hTransportTarget
  have hTG : H.twoMeetLevel a b c d ≤ G.twoMeetLevel a b c d :=
    Nat.le_findGreatest (H.twoMeetLevel_le_min a b c d)
      hTransportSource
  change G.twoMeetLevel a b c d = H.twoMeetLevel a b c d
  omega

/-- An original left 1-split keeps its bounded source witness
literally, for any cross Devlin orientation. -/
theorem finiteTwoBlockCarrier_left_oneSplit_has_witness
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hWitness : ∀ s : Nat, IsOneSplit H s → s < n →
      ∃ a b : Nat, a < n ∧ b < n ∧
        IsLeaf H a ∧ IsLeaf H b ∧
        s < a ∧ s < b ∧ H.oneMeetLevel a b = s)
    (bits : Nat → Bool)
    (s : Nat) (hsn : s < n)
    (hSplit : IsOneSplit (finiteTwoBlockCarrier H K n m bits) s) :
    ∃ a b : Nat,
      IsLeaf (finiteTwoBlockCarrier H K n m bits) a ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) b ∧
      s < a ∧ s < b ∧
      (finiteTwoBlockCarrier H K n m bits).oneMeetLevel a b = s := by
  have hSourceSplit : IsOneSplit H s :=
    (finiteTwoBlockCarrier_left_oneSplit_iff
      FH FK bits s hsn).mp hSplit
  obtain ⟨a,b,han,hbn,ha,hb,hsa,hsb,hMeet⟩ :=
    hWitness s hSourceSplit hsn
  refine ⟨a,b,
    (finiteTwoBlockCarrier_left_leaf_iff
      FH FK bits a han).mpr ha,
    (finiteTwoBlockCarrier_left_leaf_iff
      FH FK bits b hbn).mpr hb,
    hsa,hsb,?_⟩
  exact (finiteTwoBlockCarrier_left_oneMeet_exact
    FH FK bits a b han hbn).trans hMeet

/-- An original left 2-split keeps its exact bounded ordered-pair
witness, including pair ordering and full numerical two-meet. -/
theorem finiteTwoBlockCarrier_left_twoSplit_has_witness
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hWitness : ∀ s : Nat, IsTwoSplit H s → s < n →
      ∃ a b c d : Nat,
        a < b ∧ c < d ∧
        a < n ∧ b < n ∧ c < n ∧ d < n ∧
        IsLeaf H a ∧ IsLeaf H b ∧
        IsLeaf H c ∧ IsLeaf H d ∧
        s < a ∧ s < c ∧ H.twoMeetLevel a b c d = s)
    (bits : Nat → Bool)
    (s : Nat) (hsn : s < n)
    (hSplit : IsTwoSplit (finiteTwoBlockCarrier H K n m bits) s) :
    ∃ a b c d : Nat, a < b ∧ c < d ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) a ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) b ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) c ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) d ∧
      s < a ∧ s < c ∧
      (finiteTwoBlockCarrier H K n m bits).twoMeetLevel a b c d = s := by
  have hsSource : IsTwoSplit H s :=
    (finiteTwoBlockCarrier_left_twoSplit_iff
      FH FK bits s hsn).mp hSplit
  obtain ⟨a,b,c,d,hab,hcd,han,hbn,hcn,hdn,
    ha,hb,hc,hd,hsa,hsc,hMeet⟩ := hWitness s hsSource hsn
  refine ⟨a,b,c,d,hab,hcd,
    (finiteTwoBlockCarrier_left_leaf_iff FH FK bits a han).mpr ha,
    (finiteTwoBlockCarrier_left_leaf_iff FH FK bits b hbn).mpr hb,
    (finiteTwoBlockCarrier_left_leaf_iff FH FK bits c hcn).mpr hc,
    (finiteTwoBlockCarrier_left_leaf_iff FH FK bits d hdn).mpr hd,
    hsa,hsc,?_⟩
  exact (finiteTwoBlockCarrier_left_twoMeet_exact FH FK bits
    a b c d han hbn hcn hdn).trans hMeet

end DiaryLeafPriority
end ThreeUniformDiaries
