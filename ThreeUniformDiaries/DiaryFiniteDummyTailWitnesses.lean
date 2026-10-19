import ThreeUniformDiaries.DiaryFiniteDummyTailRoleCoherence

/-!
# Genuine V1/V2 split witnesses survive infinite dummy-tail extension

Every split of the countable dummy-tail carrier is a marker-defined
old finite source split. The bounded finite V/E source block
provides witnesses for every such split INSIDE its original finite
range. The tail extension preserves every original edge, role,
singleton numerical meet and full ordered-pair numerical meet
exactly, with no restriction on the chosen cross marker bits.

Thus the two global V1/V2 witness-existence axioms are valid for
EVERY split of the countable tail carrier. These are the genuine
RolePrediary witness clauses over Nat, not merely finite witnesses.
The only remaining countable pre-diary ingredients after this
stage are E1--E5 and global V3.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {n : Nat}

/-- Every countable target one-split retains a genuine ordered
pair of leaf witnesses with exact numeric singleton meet. -/
theorem finiteDummyTailCarrier_oneSplit_witness
    (P : FiniteRolePrediaryBlock H n)
    (bits : Nat → Bool)
    (s : Nat) (hs : IsOneSplit (finiteDummyTailCarrier H n bits) s) :
    ∃ a b : Nat,
      IsLeaf (finiteDummyTailCarrier H n bits) a ∧
      IsLeaf (finiteDummyTailCarrier H n bits) b ∧
      s < a ∧ s < b ∧
      (finiteDummyTailCarrier H n bits).oneMeetLevel a b = s := by
  have hsn := finiteDummyTailCarrier_oneSplit_lt P.frame bits s hs
  have hsSource : IsOneSplit H s :=
    (finiteDummyTailCarrier_old_oneSplit_iff
      P.frame bits s hsn).mp hs
  obtain ⟨a,b,han,hbn,ha,hb,hsa,hsb,hMeet⟩ :=
    P.one_split_witness s hsSource hsn
  refine ⟨a,b,
    (finiteDummyTailCarrier_old_leaf_iff
      P.frame bits a han).mpr ha,
    (finiteDummyTailCarrier_old_leaf_iff
      P.frame bits b hbn).mpr hb,
    hsa,hsb,?_⟩
  exact (finiteDummyTailCarrier_old_oneMeet_exact
    P.frame bits a b han hbn).trans hMeet

/-- Every countable target two-split retains two genuinely
ordered source leaf-pair witnesses with exact full two-meet. -/
theorem finiteDummyTailCarrier_twoSplit_witness
    (P : FiniteRolePrediaryBlock H n)
    (bits : Nat → Bool)
    (s : Nat) (hs : IsTwoSplit (finiteDummyTailCarrier H n bits) s) :
    ∃ a b c d : Nat, a < b ∧ c < d ∧
      IsLeaf (finiteDummyTailCarrier H n bits) a ∧
      IsLeaf (finiteDummyTailCarrier H n bits) b ∧
      IsLeaf (finiteDummyTailCarrier H n bits) c ∧
      IsLeaf (finiteDummyTailCarrier H n bits) d ∧
      s < a ∧ s < c ∧
      (finiteDummyTailCarrier H n bits).twoMeetLevel a b c d = s := by
  have hsn := finiteDummyTailCarrier_twoSplit_lt P.frame bits s hs
  have hsSource : IsTwoSplit H s :=
    (finiteDummyTailCarrier_old_twoSplit_iff
      P.frame bits s hsn).mp hs
  obtain ⟨a,b,c,d,hab,hcd,han,hbn,hcn,hdn,
    ha,hb,hc,hd,hsa,hsc,hMeet⟩ :=
      P.two_split_witness s hsSource hsn
  refine ⟨a,b,c,d,hab,hcd,
    (finiteDummyTailCarrier_old_leaf_iff
      P.frame bits a han).mpr ha,
    (finiteDummyTailCarrier_old_leaf_iff
      P.frame bits b hbn).mpr hb,
    (finiteDummyTailCarrier_old_leaf_iff
      P.frame bits c hcn).mpr hc,
    (finiteDummyTailCarrier_old_leaf_iff
      P.frame bits d hdn).mpr hd,
    hsa,hsc,?_⟩
  exact (finiteDummyTailCarrier_old_twoMeet_exact
    P.frame bits a b c d han hbn hcn hdn).trans hMeet

end DiaryLeafPriority
end ThreeUniformDiaries
