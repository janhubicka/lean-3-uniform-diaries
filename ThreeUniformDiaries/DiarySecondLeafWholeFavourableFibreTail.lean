import ThreeUniformDiaries.DiarySecondLeafCofinalRootedSplitCriterion

/-!
# Track A: full eventual reserved-successor saturation of a favourable second-leaf fibre

Let m be the SECOND true source leaf, with only one old selected source
leaf a, and fix a GENUINE reserved old stage f. Fix a genuine target S1
split s below f(a), with the correct source right E2 orientation and
both old numeric gap tests.

The exact fixed-target reserved second-leaf iff already proves more than
cofinality: EVERY true target F-range leaf v in the SAME rooted split
fibre, satisfying the sole remaining future-gap
f(a)+(m-a) <= v, has an ACTUAL complete reserved immediate successor
that fixes the ENTIRE old supported map f. No cofinality or
generic-richness of this fibre is assumed.

This is a local finite-source strengthening, not a fixed-new-image
persistent successor across future source horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Exact eventual saturation of a favourable rooted second-leaf
split fibre: after the *explicit* numerical bound f(a)+(m-a),
EVERY actual target true leaf v of the original F range with
oneMeet_K(f(a),v)=s is the image of a GENUINE future-order-reserved
immediate successor, literally agreeing with f on the entire old
support S_m. Only the exact source E2 sign and two old reserve
gaps are required; the fibre need not contain a generic subcopy.

The conclusion does NOT hold for a later source horizon m+1+n
without additional relative-extension hypotheses. -/
theorem RoleDiary.second_leaf_favourable_split_saturates_entire_late_fibre
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (a m s : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hsRole : IsOneSplit K s) (hsBelow : s < f a)
    (hBit : H.edge 0 (H.oneMeetLevel a m) m ↔
      ¬ K.edge 0 s (f a))
    (hGap1 : H.oneMeetLevel a m ≤ s)
    (hGap2 : s + (a - H.oneMeetLevel a m) ≤ f a) :
    ∀ v : Nat, f a + (m - a) ≤ v →
      IsLeaf K v → (∃ t : Nat, v = F t) →
      K.oneMeetLevel (f a) v = s →
      HasCompatibleReservedNextLeaf H K F f m v := by
  have haSelected : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  have haSupported : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a haSelected
  have hwLeaf : IsLeaf K (f a) :=
    P.1.leaf_role a haSupported ha
  intro v hLate hvLeaf hvRange hMeet
  have hwLtV : f a < v := by
    have hPositive : 0 < m - a := Nat.sub_pos_of_lt ham
    omega
  have hsLtV : s < v := lt_trans hsBelow hwLtV
  have hOpp :
      ¬ (K.edge 0 s (f a) ↔ K.edge 0 s v) :=
    DK.oneSplit_witness_opposite_marker s (f a) v
      hsRole hwLeaf hvLeaf hsBelow hsLtV hMeet
  have hTargetBit :
      (¬ K.edge 0 s (f a)) ↔ K.edge 0 s v := by
    tauto
  have hRight :
      H.edge 0 (H.oneMeetLevel a m) m ↔
        K.edge 0 (K.oneMeetLevel (f a) v) v := by
    rw [hMeet]
    exact hBit.trans hTargetBit
  have hGap1' :
      H.oneMeetLevel a m ≤ K.oneMeetLevel (f a) v := by
    simpa only [hMeet] using hGap1
  have hGap2' :
      K.oneMeetLevel (f a) v +
        (a - H.oneMeetLevel a m) ≤ f a := by
    simpa only [hMeet] using hGap2
  obtain ⟨g,Q,hKeep,hNew⟩ :=
    (DH.second_leaf_fixed_v_reserved_successor_iff
      DK F f a m v ha hm ham hOld P hvLeaf hvRange).mpr
        ⟨hRight,hGap1',hGap2',hLate⟩
  have hOldCompatible : CofinalDiaryStageCompatible H m f g :=
    P.1.successor_compatible_of_selected_leaf_agreement
      Q.1 hKeep
  exact ⟨g,Q,hOldCompatible,hNew⟩

end DiaryLeafPriority
end ThreeUniformDiaries
