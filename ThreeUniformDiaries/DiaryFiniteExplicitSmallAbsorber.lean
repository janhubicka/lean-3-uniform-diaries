import ThreeUniformDiaries.DiaryFinitePointedPositivePairEmbedding
import ThreeUniformDiaries.DiaryFiniteThreeLeafAlternation

/-!
# Every genuine flip of the explicit nine-vertex target contains the
# prescribed six-vertex diary with ALL numerical meets preserved

The source and target have already been certified as genuine
bounded finite V/E/S diaries. In any flip of the target, the
roles and the numerical singleton meets (6,7)=4 and (7,8)=4
remain unchanged. The three-leaf alternation theorem therefore
ensures that one of the consecutive pairs (6,7) or (7,8) has
its first leaf negative and second leaf positive at split 4.

The independently verified positive-pointed-pair embedding lemma
then gives a full bounded, induced, all-meet preserving copy of
the six-vertex source, along one of the two explicit vertex maps.
This is a complete proof of a concrete NONRIGID instance of the
second finite flip property, but not of the general theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The first fully certified non-rigid instance of strong finite
target-flip absorption: a genuine nine-vertex diary absorbs the
specified six-vertex diary under EVERY identity preembedding flip,
using one of two protected copies selected by its E2 orientation.

This does not replace the general lower-bound geometry. -/
theorem smallFlipTarget_absorbs_smallFlipSource :
    AbsorbsEveryTargetFlipInside
      smallFlipSource smallFlipTarget 6 9 := by
  intro T FT
  have hT4 : IsOneSplit T 4 :=
    ((FT.role_iff 4 smallFlipTarget_oneSplit4.1 (by omega)).2.1).mp
      smallFlipTarget_oneSplit4
  have hT6 : IsLeaf T 6 :=
    ((FT.role_iff 6 smallFlipTarget_leaf6.1 (by omega)).1).mp
      smallFlipTarget_leaf6
  have hT7 : IsLeaf T 7 :=
    ((FT.role_iff 7 smallFlipTarget_leaf7.1 (by omega)).1).mp
      smallFlipTarget_leaf7
  have hT8 : IsLeaf T 8 :=
    ((FT.role_iff 8 smallFlipTarget_leaf8.1 (by omega)).1).mp
      smallFlipTarget_leaf8
  have hMeet67 : T.oneMeetLevel 6 7 = 4 :=
    (FT.leaf_oneMeet 6 7 (by omega) (by omega)
      smallFlipTarget_leaf6 smallFlipTarget_leaf7).symm.trans
        smallFlipTarget_meet_6_7
  have hMeet78 : T.oneMeetLevel 7 8 = 4 :=
    (FT.leaf_oneMeet 7 8 (by omega) (by omega)
      smallFlipTarget_leaf7 smallFlipTarget_leaf8).symm.trans
        smallFlipTarget_meet_7_8
  have hAlternation :=
    FT.three_leaf_alternating_oneSplit
      4 6 7 8 smallFlipTarget_oneSplit4
      (by omega) (by omega) (by omega) (by omega)
      smallFlipTarget_leaf6 smallFlipTarget_leaf7
      smallFlipTarget_leaf8
      smallFlipTarget_meet_6_7 smallFlipTarget_meet_7_8
  rcases hAlternation with hLeft | hRight
  · obtain ⟨hNegative,hPositive,_⟩ := hLeft
    exact smallFlipSource_embeds_of_positive_oneSplit
      FT.target_diary 4 6 7 hT4
      (by omega) (by omega) (by omega)
      hT6 hT7 hMeet67 hNegative hPositive
  · obtain ⟨hNegative,hPositive,_⟩ := hRight
    exact smallFlipSource_embeds_of_positive_oneSplit
      FT.target_diary 4 7 8 hT4
      (by omega) (by omega) (by omega)
      hT7 hT8 hMeet78 hNegative hPositive

/-- The quantified target B really is a finite diary, and
every finite flip of it admits a full bounded source embedding. -/
theorem exists_concrete_nonrigid_finite_flip_absorber :
    ∃ B : Ordered3Graph Nat,
      FiniteRoleDiaryBlock B 9 ∧
      AbsorbsEveryTargetFlipInside smallFlipSource B 6 9 := by
  exact ⟨smallFlipTarget,smallFlipTarget_is_finiteDiary,
    smallFlipTarget_absorbs_smallFlipSource⟩

end DiaryLeafPriority
end ThreeUniformDiaries
