import ThreeUniformDiaries.DiaryFiniteOrderedSumRightExactMeets
import ThreeUniformDiaries.DiaryFiniteOrderedSumRoles

/-!
# Split witnesses in the translated right finite diary block

A finite source block is equipped with *bounded* V1/V2 witnesses:
the witness leaves and the split all occur below the finite block
length. Unlike a full RolePrediary on Nat, this is consistent with
finite edge support and makes no spurious claims about vertices
outside the finite frame.

The numerical right-meet theorems transport every genuine source
strict split witness to an exact witness at the translated target
split. Thus the two right-block split-witness obligations hold for
arbitrary cross-copy orientation bits.

The ambient ordered sum is not yet claimed to be a pre-diary:
right-right V3, target witness coverage beyond the two blocks,
and the appropriate finite-language output interface remain
separate obligations.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Transport the bounded genuine singleton witness at every
right-block target 1-split. The witness record includes source
length bounds, which are essential for a *finite* source block. -/
theorem finiteTwoBlockCarrier_right_oneSplit_has_witness
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hShape : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (hWitness : ∀ s : Nat, IsOneSplit K s → s < m →
      ∃ a b : Nat, a < m ∧ b < m ∧
        IsLeaf K a ∧ IsLeaf K b ∧
        s < a ∧ s < b ∧ K.oneMeetLevel a b = s)
    (bits : Nat → Bool)
    (s : Nat) (hs3 : 3 ≤ s) (hsm : s < m)
    (hSplit : IsOneSplit (finiteTwoBlockCarrier H K n m bits)
      (rightBlockImage n s)) :
    ∃ a b : Nat,
      IsLeaf (finiteTwoBlockCarrier H K n m bits) a ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) b ∧
      rightBlockImage n s < a ∧ rightBlockImage n s < b ∧
      (finiteTwoBlockCarrier H K n m bits).oneMeetLevel a b =
        rightBlockImage n s := by
  have hsSource : IsOneSplit K s :=
    (finiteTwoBlockCarrier_right_oneSplit_iff
      FH FK bits s hs3 hsm).mp hSplit
  obtain ⟨a,b,ham,hbm,ha,hb,hsa,hsb,hMeet⟩ :=
    hWitness s hsSource hsm
  have hMon := rightBlockImage_strictMono n FH.length_ge_three
  refine ⟨rightBlockImage n a, rightBlockImage n b,
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits a ha.1 ham).mpr ha,
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits b hb.1 hbm).mpr hb,
    hMon hsa, hMon hsb, ?_⟩
  exact finiteTwoBlockCarrier_right_oneMeet_exact
    FH FK hShape bits s a b hs3
    ha.1 ham ha hb.1 hbm hb hsa hsb hMeet

/-- Transport every bounded full ordered-pair witness at a
right-block target 2-split, including literal target leaf roles,
pair ordering, both strict bounds and the exact numerical meet. -/
theorem finiteTwoBlockCarrier_right_twoSplit_has_witness
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hShape : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (hWitness : ∀ s : Nat, IsTwoSplit K s → s < m →
      ∃ a b c d : Nat,
        a < b ∧ c < d ∧
        a < m ∧ b < m ∧ c < m ∧ d < m ∧
        IsLeaf K a ∧ IsLeaf K b ∧
        IsLeaf K c ∧ IsLeaf K d ∧
        s < a ∧ s < c ∧
        K.twoMeetLevel a b c d = s)
    (bits : Nat → Bool)
    (s : Nat) (hs3 : 3 ≤ s) (hsm : s < m)
    (hSplit : IsTwoSplit (finiteTwoBlockCarrier H K n m bits)
      (rightBlockImage n s)) :
    ∃ a b c d : Nat, a < b ∧ c < d ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) a ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) b ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) c ∧
      IsLeaf (finiteTwoBlockCarrier H K n m bits) d ∧
      rightBlockImage n s < a ∧ rightBlockImage n s < c ∧
      (finiteTwoBlockCarrier H K n m bits).twoMeetLevel a b c d =
        rightBlockImage n s := by
  have hsSource : IsTwoSplit K s :=
    (finiteTwoBlockCarrier_right_twoSplit_iff
      FH FK bits s hs3 hsm).mp hSplit
  obtain ⟨a,b,c,d,hab,hcd,ham,hbm,hcm,hdm,
    ha,hb,hc,hd,hsa,hsc,hMeet⟩ :=
      hWitness s hsSource hsm
  have hMon := rightBlockImage_strictMono n FH.length_ge_three
  refine ⟨rightBlockImage n a, rightBlockImage n b,
    rightBlockImage n c, rightBlockImage n d,
    hMon hab, hMon hcd,
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits a ha.1 ham).mpr ha,
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits b hb.1 hbm).mpr hb,
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits c hc.1 hcm).mpr hc,
    (finiteTwoBlockCarrier_right_leaf_iff
      FH FK bits d hd.1 hdm).mpr hd,
    hMon hsa, hMon hsc, ?_⟩
  exact finiteTwoBlockCarrier_right_twoMeet_exact
    FH FK hShape bits s a b c d hs3
    ha.1 ham ha hb.1 hbm hb
    hc.1 hcm hc hd.1 hdm hd
    hsa hsc hMeet

end DiaryLeafPriority
end ThreeUniformDiaries
