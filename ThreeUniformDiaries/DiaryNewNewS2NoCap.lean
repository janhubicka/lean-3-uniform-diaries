import ThreeUniformDiaries.DiaryExactS2Cap
import ThreeUniformDiaries.DiaryCofinalGenericNewNewS2E3Profile

/-!
# Track A: new-new pair meets with distinct old first leaves cannot cap

In a full diary, consider two ordered leaf pairs (a,v) and (b,v),
where a<b<v and a,b,v are genuine leaves. The full pair meet
cannot attain the cap a: the verified exact manuscript S2 cap lemma
forces equality of first coordinates whenever the cap occurs,
contradicting a<b. Therefore the meet is either marker 1 or a
GENUINE two-split.

This is stronger than the three-way S2 role classification in the
checked cofinal new-new profile theorem. No arbitrary target split
or E3 sign is prescribed; it is a shape restriction, not relative
candidate existence or countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Two distinct genuine old first coordinates cannot produce a
capped full pair meet when both pairs share the same later leaf.
The only possibilities are marker 1 or a genuine target two-split. -/
theorem RoleDiary.newNewPairMeet_marker_or_twoSplit
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (a b v : Nat)
    (hab : a < b) (hav : a < v) (hbv : b < v)
    (ha : IsLeaf K a) (hb : IsLeaf K b) (hv : IsLeaf K v) :
    K.twoMeetLevel a v b v = 1 ∨
      IsTwoSplit K (K.twoMeetLevel a v b v) := by
  rcases DK.pair_meets_exact_manuscript
      a v b v hav hbv ha hv hb hv with
    hOne | ⟨_hCap, hEq⟩ | hTwo
  · exact Or.inl hOne
  · exact False.elim ((ne_of_lt hab) hEq)
  · exact Or.inr hTwo

end DiaryLeafPriority
end ThreeUniformDiaries
