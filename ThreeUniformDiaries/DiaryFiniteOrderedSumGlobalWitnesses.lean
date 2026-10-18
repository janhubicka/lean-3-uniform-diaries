import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.DiaryFiniteOrderedSumRoleCases
import ThreeUniformDiaries.DiaryFiniteOrderedSumLeftExactMeets
import ThreeUniformDiaries.DiaryFiniteOrderedSumRightExactMeets

/-!
# Global bounded split-witness transport for finite ordered sums

The source blocks are genuine finite V/E pre-diaries, with every
1-split and 2-split witnessed by source leaves INSIDE their own
finite edge frame. The ordered sum preserves the exact numeric
meets of left witness leaves and translates exact strict right
witness meets. Thus each actual target split has a witness with
all witness leaves INSIDE the combined finite carrier bound.

The finite role-case analysis is essential here: no other
target splits are possible. Unlike earlier unbounded witness
theorems, the conclusions have the exact bounded form required
by the FiniteRolePrediaryBlock record. No source S1/S2 is used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Full FINITE V1 witness condition for every actual target
one-split: bounded leaves, correct roles, strict positions,
and the exact numerical singleton meet. -/
theorem finiteTwoBlockCarrier_oneSplit_bounded_witness
    (PH : FiniteRolePrediaryBlock H n)
    (PK : FiniteRolePrediaryBlock K m)
    (bits : Nat → Bool)
    (s : Nat) (hs : IsOneSplit (finiteTwoBlockCarrier H K n m bits) s)
    (hsBound : s < finiteTwoBlockLength n m) :
    ∃ a b : Nat,
      a < finiteTwoBlockLength n m ∧
      b < finiteTwoBlockLength n m ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) a ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) b ∧
      s < a ∧ s < b ∧
      (finiteTwoBlockCarrier H K n m bits).oneMeetLevel a b = s := by
  rcases finiteTwoBlock_oneSplit_cases PH.frame PK.frame
      bits s hs hsBound with
      ⟨hsn,hSource⟩ | ⟨v,hv3,hvm,hSource,hImage⟩
  · obtain ⟨a,b,han,hbn,ha,hb,hsa,hsb,hMeet⟩ :=
      PH.one_split_witness s hSource hsn
    have hN : n ≤ finiteTwoBlockLength n m := by
      unfold finiteTwoBlockLength
      have hm3 := PK.frame.length_ge_three
      omega
    refine ⟨a,b,by omega,by omega,
      (finiteTwoBlockCarrier_left_leaf_iff
        PH.frame PK.frame bits a han).mpr ha,
      (finiteTwoBlockCarrier_left_leaf_iff
        PH.frame PK.frame bits b hbn).mpr hb,
      hsa,hsb,?_⟩
    exact (finiteTwoBlockCarrier_left_oneMeet_exact
      PH.frame PK.frame bits a b han hbn).trans hMeet
  · subst s
    obtain ⟨a,b,ham,hbm,ha,hb,hva,hvb,hMeet⟩ :=
      PK.one_split_witness v hSource hvm
    have hMon := rightBlockImage_strictMono
      n PH.frame.length_ge_three
    refine ⟨rightBlockImage n a,rightBlockImage n b,
      rightBlockImage_lt_finiteTwoBlockLength n m a
        PH.frame.length_ge_three PK.frame.length_ge_three
        ha.1 ham,
      rightBlockImage_lt_finiteTwoBlockLength n m b
        PH.frame.length_ge_three PK.frame.length_ge_three
        hb.1 hbm,
      (finiteTwoBlockCarrier_right_leaf_iff
        PH.frame PK.frame bits a ha.1 ham).mpr ha,
      (finiteTwoBlockCarrier_right_leaf_iff
        PH.frame PK.frame bits b hb.1 hbm).mpr hb,
      hMon hva,hMon hvb,?_⟩
    exact finiteTwoBlockCarrier_right_oneMeet_exact
      PH.frame PK.frame PK.permitted_edge bits v a b hv3
      ha.1 ham ha hb.1 hbm hb hva hvb hMeet

/-- Full FINITE V2 witness condition for every actual target
two-split, including two increasing leaf pairs and an exact
strict numerical full two-meet at that split. -/
theorem finiteTwoBlockCarrier_twoSplit_bounded_witness
    (PH : FiniteRolePrediaryBlock H n)
    (PK : FiniteRolePrediaryBlock K m)
    (bits : Nat → Bool)
    (s : Nat) (hs : IsTwoSplit (finiteTwoBlockCarrier H K n m bits) s)
    (hsBound : s < finiteTwoBlockLength n m) :
    ∃ a b c d : Nat,
      a < b ∧ c < d ∧
      a < finiteTwoBlockLength n m ∧
      b < finiteTwoBlockLength n m ∧
      c < finiteTwoBlockLength n m ∧
      d < finiteTwoBlockLength n m ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) a ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) b ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) c ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) d ∧
      s < a ∧ s < c ∧
      (finiteTwoBlockCarrier H K n m bits).twoMeetLevel a b c d = s := by
  rcases finiteTwoBlock_twoSplit_cases PH.frame PK.frame
      bits s hs hsBound with
      ⟨hsn,hSource⟩ | ⟨v,hv3,hvm,hSource,hImage⟩
  · obtain ⟨a,b,c,d,hab,hcd,han,hbn,hcn,hdn,
      ha,hb,hc,hd,hsa,hsc,hMeet⟩ :=
      PH.two_split_witness s hSource hsn
    have hN : n ≤ finiteTwoBlockLength n m := by
      unfold finiteTwoBlockLength
      have hm3 := PK.frame.length_ge_three
      omega
    refine ⟨a,b,c,d,hab,hcd,
      by omega,by omega,by omega,by omega,
      (finiteTwoBlockCarrier_left_leaf_iff
        PH.frame PK.frame bits a han).mpr ha,
      (finiteTwoBlockCarrier_left_leaf_iff
        PH.frame PK.frame bits b hbn).mpr hb,
      (finiteTwoBlockCarrier_left_leaf_iff
        PH.frame PK.frame bits c hcn).mpr hc,
      (finiteTwoBlockCarrier_left_leaf_iff
        PH.frame PK.frame bits d hdn).mpr hd,
      hsa,hsc,?_⟩
    exact (finiteTwoBlockCarrier_left_twoMeet_exact
      PH.frame PK.frame bits a b c d han hbn hcn hdn).trans hMeet
  · subst s
    obtain ⟨a,b,c,d,hab,hcd,ham,hbm,hcm,hdm,
      ha,hb,hc,hd,hva,hvc,hMeet⟩ :=
      PK.two_split_witness v hSource hvm
    have hMon := rightBlockImage_strictMono
      n PH.frame.length_ge_three
    refine ⟨rightBlockImage n a,rightBlockImage n b,
      rightBlockImage n c,rightBlockImage n d,
      hMon hab,hMon hcd,
      rightBlockImage_lt_finiteTwoBlockLength n m a
        PH.frame.length_ge_three PK.frame.length_ge_three ha.1 ham,
      rightBlockImage_lt_finiteTwoBlockLength n m b
        PH.frame.length_ge_three PK.frame.length_ge_three hb.1 hbm,
      rightBlockImage_lt_finiteTwoBlockLength n m c
        PH.frame.length_ge_three PK.frame.length_ge_three hc.1 hcm,
      rightBlockImage_lt_finiteTwoBlockLength n m d
        PH.frame.length_ge_three PK.frame.length_ge_three hd.1 hdm,
      (finiteTwoBlockCarrier_right_leaf_iff
        PH.frame PK.frame bits a ha.1 ham).mpr ha,
      (finiteTwoBlockCarrier_right_leaf_iff
        PH.frame PK.frame bits b hb.1 hbm).mpr hb,
      (finiteTwoBlockCarrier_right_leaf_iff
        PH.frame PK.frame bits c hc.1 hcm).mpr hc,
      (finiteTwoBlockCarrier_right_leaf_iff
        PH.frame PK.frame bits d hd.1 hdm).mpr hd,
      hMon hva,hMon hvc,?_⟩
    exact finiteTwoBlockCarrier_right_twoMeet_exact
      PH.frame PK.frame PK.permitted_edge bits v a b c d hv3
      ha.1 ham ha hb.1 hbm hb
      hc.1 hcm hc hd.1 hdm hd
      hva hvc hMeet

end DiaryLeafPriority
end ThreeUniformDiaries
