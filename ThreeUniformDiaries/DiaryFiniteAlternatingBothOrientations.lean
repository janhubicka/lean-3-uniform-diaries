import ThreeUniformDiaries.DiaryFinitePointedNegativePairEmbedding
import ThreeUniformDiaries.DiaryFiniteGeneralThreeLeafAbsorber
import ThreeUniformDiaries.DiaryFiniteExplicitSmallAbsorber

/-!
# One alternating three-leaf gadget absorbs BOTH opposite sources

For leaves a<b<c with a∧b=b∧c=s at a genuine one-split,
the E2 bits of adjacent pairs differ. Among the two pairs,
one has positive RIGHT orientation (the original source),
and the other has positive LEFT orientation (its genuine
opposite source flip).

For every genuine target flip these exact adjacent leaf
meets survive. The two independent protected pointed-pair
embedding lemmas therefore give copies of BOTH orientations
in the SAME target flip, with full mixed meet preservation.

This is a strong concrete simultaneous absorption theorem,
not a general construction for arbitrary source diaries.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every finite target with an alternating three-leaf one-split
pattern absorbs the OPPOSITE six-vertex source under every flip. -/
theorem absorbs_smallFlipSourceOpposite_of_alternating_three_leaves
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
    AbsorbsEveryTargetFlipInside smallFlipSourceOpposite B 6 k := by
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
  have hDiffAB : ¬ (T.edge 0 s a ↔ T.edge 0 s b) :=
    E_oneSplit_distinguishing_zero_bit
      FT.target_diary.prediary.permitted_edge
      s a b hTs hab hsa hMeetAB
  have hDiffBC : ¬ (T.edge 0 s b ↔ T.edge 0 s c) :=
    E_oneSplit_distinguishing_zero_bit
      FT.target_diary.prediary.permitted_edge
      s b c hTs hbc (by omega) hMeetBC
  by_cases hMiddlePositive : T.edge 0 s b
  · have hLastNegative : ¬ T.edge 0 s c := by
      intro hcPos
      exact hDiffBC (iff_of_true hMiddlePositive hcPos)
    exact smallFlipSourceOpposite_embeds_of_negative_oneSplit
      FT.target_diary s b c hTs
      (by omega) hbc hck hTb hTc hMeetBC
      hMiddlePositive hLastNegative
  · have hFirstPositive : T.edge 0 s a := by
      by_contra haNeg
      exact hDiffAB (iff_of_false haNeg hMiddlePositive)
    exact smallFlipSourceOpposite_embeds_of_negative_oneSplit
      FT.target_diary s a b hTs
      hsa hab (by omega) hTa hTb hMeetAB
      hFirstPositive hMiddlePositive

/-- The two genuine six-vertex source orientations are
simultaneously absorbed by every target flip. The two copies
need not have disjoint images (nor do we assert that).
Their existence is enough for the finite orbit covering property. -/
theorem alternating_three_leaves_absorbs_both_six_vertex_sources
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
    AbsorbsEveryTargetFlipInside smallFlipSource B 6 k ∧
    AbsorbsEveryTargetFlipInside smallFlipSourceOpposite B 6 k := by
  exact ⟨
    absorbs_smallFlipSource_of_alternating_three_leaves
      DB s a b c hs hsa hab hbc hck ha hb hc hmAB hmBC,
    absorbs_smallFlipSourceOpposite_of_alternating_three_leaves
      DB s a b c hs hsa hab hbc hck ha hb hc hmAB hmBC
  ⟩

/-- In particular, EVERY genuine target flip of the concrete
nine-vertex diary contains fully protected induced copies of
BOTH distinct six-vertex source orientations. -/
theorem smallFlipTarget_absorbs_both_source_orientations :
    AbsorbsEveryTargetFlipInside
      smallFlipSource smallFlipTarget 6 9 ∧
    AbsorbsEveryTargetFlipInside
      smallFlipSourceOpposite smallFlipTarget 6 9 := by
  exact alternating_three_leaves_absorbs_both_six_vertex_sources
    smallFlipTarget_is_finiteDiary
    4 6 7 8 smallFlipTarget_oneSplit4
    (by omega) (by omega) (by omega) (by omega)
    smallFlipTarget_leaf6 smallFlipTarget_leaf7 smallFlipTarget_leaf8
    smallFlipTarget_meet_6_7 smallFlipTarget_meet_7_8

end DiaryLeafPriority
end ThreeUniformDiaries
