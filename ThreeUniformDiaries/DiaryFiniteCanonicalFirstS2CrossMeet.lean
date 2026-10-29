import ThreeUniformDiaries.DiaryFiniteCanonicalSharedSourcePairCodes
import ThreeUniformDiaries.DiaryFiniteCanonicalSourceRankMap

/-!
# The source-fixed E3 witness detects actual causal branch separation

Two canonical source flips with a common sign-rooted node at a
genuine 2-split and opposite selected E3 witness bits have
identical complete predecessor pair codes below the split,
even though their current E3 bits are opposite.

The proven positivity-free crossbranch pair-meet theorem then
shows that the two copies of the SAME selected ordered pair
have full numerical meet exactly at that shared split in the
ACTUAL finite causal V/E pre-diary. No abstract free Boolean
coordinates, crossbranch S1/S2, or target flip absorption
are assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

theorem finiteCanonical_firstS2Bit_causes_crossTwoMeet
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s : FiniteTwoSplitIndex A n)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s.val.val =
      (finiteCanonicalSignRootedFamily DA).node j s.val.val)
    (hDiff :
      ((finiteCanonicalSignRootedFamily DA).signature i).2 s ≠
      ((finiteCanonicalSignRootedFamily DA).signature j).2 s) :
    let W := finiteSelectedS2Witness DA s
    (finiteCanonicalCausalMarkerGraph DA).twoMeetLevel
      (finiteCanonicalSourceRankMap DA i W.a)
      (finiteCanonicalSourceRankMap DA i W.b)
      (finiteCanonicalSourceRankMap DA j W.a)
      (finiteCanonicalSourceRankMap DA j W.b) =
      finiteCanonicalSourceRankMap DA i s.val.val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let W := finiteSelectedS2Witness DA s
  have hCode :
      twoCode (F.graph i) s.val.val W.a W.b =
        twoCode (F.graph j) s.val.val W.a W.b :=
    finiteCanonicalSignRooted_source_twoCode_at_shared_split
      DA i j s.val.val s.property hShared
      W.a W.b W.hsa.le W.hab W.hbn
  have hE3 : ¬ ((F.graph i).edge s.val.val W.a W.b ↔
      (F.graph j).edge s.val.val W.a W.b) :=
    finiteCanonicalSignRooted_selected_pair_E3_different
      DA i j s hDiff
  have han : W.a < n := lt_trans W.hab W.hbn
  have haI : IsLeaf (F.graph i) W.a :=
    ((F.flip i).role_iff W.a W.ha.1 han).1.mp W.ha
  have hbI : IsLeaf (F.graph i) W.b :=
    ((F.flip i).role_iff W.b W.hb.1 W.hbn).1.mp W.hb
  have haJ : IsLeaf (F.graph j) W.a :=
    ((F.flip j).role_iff W.a W.ha.1 han).1.mp W.ha
  have hbJ : IsLeaf (F.graph j) W.b :=
    ((F.flip j).role_iff W.b W.hb.1 W.hbn).1.mp W.hb
  have h := finiteCanonicalCausalMarkerGraph_crossTwoMeet_exact_at_sharedSplit
    DA i j s.val.val W.a W.b W.a W.b
    s.property s.val.isLt hShared
    W.hab W.hab W.hbn W.hbn
    W.hsa W.hsa
    haI hbI haJ hbJ hCode hE3
  simpa only [finiteCanonicalSourceRankMap_of_lt DA i W.a han,
    finiteCanonicalSourceRankMap_of_lt DA i W.b W.hbn,
    finiteCanonicalSourceRankMap_of_lt DA j W.a han,
    finiteCanonicalSourceRankMap_of_lt DA j W.b W.hbn,
    finiteCanonicalSourceRankMap_of_lt DA i s.val.val s.val.isLt]
    using h

end DiaryLeafPriority
end ThreeUniformDiaries
