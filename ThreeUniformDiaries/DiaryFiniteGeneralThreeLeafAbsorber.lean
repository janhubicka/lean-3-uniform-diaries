import ThreeUniformDiaries.DiaryFinitePointedPositivePairEmbedding
import ThreeUniformDiaries.DiaryFiniteThreeLeafAlternation

/-!
# Any finite diary containing an alternating three-leaf gadget
# absorbs the six-vertex source under every genuine target flip

There is no need to enumerate all target flips and no need to
choose a global coherent family of source flips. If a finite
diary B contains one split s and three leaves a<b<c with exact
adjacent singleton meets at s, every flip T of B still has
that configuration. Its V/E conditions make the three E2
incidences alternate. One of (a,b), (b,c) is oriented exactly
as the six-vertex source smallFlipSource.

The verified positive one-split pair embedding lemma then
provides a FULL bounded induced all-mixed-meet copy of
smallFlipSource in T. The same gadget can lie anywhere in a
larger finite diary, with arbitrary other vertices and
2-splits.

This is an unconditional sufficient criterion for the
six-vertex example, not the general second finite flip theorem
for arbitrary source diaries.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A single alternating triple at any genuine one-split
is a sufficient witness for strong bounded absorption of
the six-vertex non-rigid source under EVERY flip of the
ambient target diary. No restriction on other target edges
or on the number of target split vertices is needed. -/
theorem absorbs_smallFlipSource_of_alternating_three_leaves
    {B : Ordered3Graph Nat} {k : Nat}
    (DB : FiniteRoleDiaryBlock B k)
    (s a b c : Nat)
    (hs : IsOneSplit B s)
    (hsa : s < a) (hab : a < b) (hbc : b < c)
    (hck : c < k)
    (ha : IsLeaf B a) (hb : IsLeaf B b)
    (hc : IsLeaf B c)
    (hmAB : B.oneMeetLevel a b = s)
    (hmBC : B.oneMeetLevel b c = s) :
    AbsorbsEveryTargetFlipInside smallFlipSource B 6 k := by
  intro T FT
  have hTs : IsOneSplit T s :=
    ((FT.role_iff s hs.1 (by omega)).2.1).mp hs
  have hTa : IsLeaf T a :=
    ((FT.role_iff a ha.1 (by omega)).1).mp ha
  have hTb : IsLeaf T b :=
    ((FT.role_iff b hb.1 (by omega)).1).mp hb
  have hTc : IsLeaf T c :=
    ((FT.role_iff c hc.1 hck).1).mp hc
  have hMeetAB : T.oneMeetLevel a b = s :=
    (FT.leaf_oneMeet a b (by omega) (by omega) ha hb).symm.trans hmAB
  have hMeetBC : T.oneMeetLevel b c = s :=
    (FT.leaf_oneMeet b c (by omega) hck hb hc).symm.trans hmBC
  have hAlternation :=
    FT.three_leaf_alternating_oneSplit
      s a b c hs hsa hab hbc hck ha hb hc hmAB hmBC
  rcases hAlternation with hLeft | hRight
  · obtain ⟨hNegative,hPositive,_hMarker⟩ := hLeft
    exact smallFlipSource_embeds_of_positive_oneSplit
      FT.target_diary s a b hTs hsa hab (by omega)
      hTa hTb hMeetAB hNegative hPositive
  · obtain ⟨hNegative,hPositive,_hMarker⟩ := hRight
    exact smallFlipSource_embeds_of_positive_oneSplit
      FT.target_diary s b c hTs (by omega) hbc hck
      hTb hTc hMeetBC hNegative hPositive

end DiaryLeafPriority
end ThreeUniformDiaries
