import ThreeUniformDiaries.DiaryFiniteCanonicalCausalCrossTwoMeet
import ThreeUniformDiaries.DiaryFiniteDummyTailOldMeets
import ThreeUniformDiaries.DiaryOnePassOldSplitWitnessTransport

/-!
# Exact cross-copy S2 meets through the real countable completion

A dummy-tail completion does not alter any old finite full pair
meet (including cross-branch meets). At a genuine old 2-split the
one-pass event block is EMPTY and the existing old-two-split
transport theorem applies to arbitrary ordered pairs of old
source leaves. Nothing in that theorem requires the leaf pairs
to belong to a single embedded source diary.

This gives a reusable exact geometric transfer for cross-branch
pair witnesses, not merely a within-branch FiniteMeetEmbedding.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The one-pass target of any genuine dummy-tail V/E pre-diary
preserves a cross-copy full pair meet at an original finite
2-split. No single-source-branch assumption is made. -/
theorem finiteDummyTail_onePass_crossTwoMeet_exact
    {G : Ordered3Graph Nat} {N : Nat}
    (FG : FiniteDiaryEdgeFrame G N)
    (bits : Nat → Bool)
    (P : RolePrediary (finiteDummyTailCarrier G N bits))
    (s a b c d : Nat)
    (hs : IsTwoSplit G s)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf G a) (hb : IsLeaf G b)
    (hc : IsLeaf G c) (hd : IsLeaf G d)
    (hsa : s < a) (hsc : s < c)
    (han : a < N) (hbn : b < N)
    (hcn : c < N) (hdn : d < N)
    (hMeet : G.twoMeetLevel a b c d = s) :
    (onePassRawTarget (finiteDummyTailCarrier G N bits)).twoMeetLevel
        (onePassOldImage (finiteDummyTailCarrier G N bits) a)
        (onePassOldImage (finiteDummyTailCarrier G N bits) b)
        (onePassOldImage (finiteDummyTailCarrier G N bits) c)
        (onePassOldImage (finiteDummyTailCarrier G N bits) d) =
      onePassOldImage (finiteDummyTailCarrier G N bits) s := by
  let H := finiteDummyTailCarrier G N bits
  have hsN : s < N := by omega
  have hRole (u : Nat) (hu : u < N) :=
    finiteDummyTailCarrier_old_role_bits FG bits u hu
  have hLeaf (u : Nat) (hu : IsLeaf G u) (hun : u < N) :
      IsLeaf H u := by
    have h := hRole u hun
    exact ⟨hu.1,
      fun he => hu.2.1 (h.1.mp he),
      fun he => hu.2.2 (h.2.mp he)⟩
  have hsH : IsTwoSplit H s := by
    have h := hRole s hsN
    exact ⟨hs.1, fun he => hs.2.1 (h.1.mp he),
      h.2.mpr hs.2.2⟩
  have hMeetH : H.twoMeetLevel a b c d = s := by
    have h := finiteDummyTailCarrier_old_twoMeet_exact FG bits
      a b c d han hbn hcn hdn
    exact h.trans hMeet
  exact onePass_oldTwoSplit_meet_exact
    P s a b c d hsH hab hcd
    (hLeaf a ha han) (hLeaf b hb hbn)
    (hLeaf c hc hcn) (hLeaf d hd hdn)
    hsa hsc hMeetH

end DiaryLeafPriority
end ThreeUniformDiaries
