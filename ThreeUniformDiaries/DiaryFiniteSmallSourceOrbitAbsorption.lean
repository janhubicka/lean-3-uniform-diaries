import ThreeUniformDiaries.DiaryFiniteAlternatingBothOrientations
import ThreeUniformDiaries.DiaryFiniteSixVertexFlipClassification

/-!
# Every genuine flip of the small source embeds in every target flip

We have now proved:
1. the genuine six-vertex source diary flip orbit is EXACTLY
   {smallFlipSource, smallFlipSourceOpposite};
2. any finite diary containing an alternating three-leaf
   one-split configuration absorbs each of these two sources
   under EVERY genuine target flip.

This immediately gives the genuinely TWO-SIDED, orbit-to-orbit
finite embedding theorem: every source flip embeds boundedly,
induced and with ALL mixed meets into EVERY target flip.

This is strictly stronger than the original second finite flip
property for this particular non-rigid source, and is witnessed
by the concrete nine-vertex target. It does NOT imply the
general property for arbitrary source diaries.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An alternating triple of leaves forces simultaneous
strong absorption of the ENTIRE genuine flip orbit of the
six-vertex source, not merely one preferred orientation. -/
theorem absorbs_all_small_source_flips_of_alternating_three_leaves
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
    ∀ P : Ordered3Graph Nat,
      FiniteDiaryFlip smallFlipSource P 6 →
      AbsorbsEveryTargetFlipInside P B 6 k := by
  obtain ⟨hBase,hOpposite⟩ :=
    alternating_three_leaves_absorbs_both_six_vertex_sources
      DB s a b c hs hsa hab hbc hck ha hb hc hmAB hmBC
  intro P FP
  rcases smallFlipSource_all_flips_are_two FP with h | h
  · rw [h]
    exact hBase
  · rw [h]
    exact hOpposite

/-- The concrete nine-vertex target is universal over BOTH
the genuine source and target flip orbits: for every pair of
finite flips P of the source and T of the target there is
a bounded, fully induced and ALL-MEET preserving embedding
of P into T. -/
theorem smallFlipTarget_absorbs_entire_small_source_orbit :
    ∀ (P T : Ordered3Graph Nat),
      FiniteDiaryFlip smallFlipSource P 6 →
      FiniteDiaryFlip smallFlipTarget T 9 →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding P T 6 9 f := by
  have hUniversal :=
    absorbs_all_small_source_flips_of_alternating_three_leaves
      smallFlipTarget_is_finiteDiary
      4 6 7 8 smallFlipTarget_oneSplit4
      (by omega) (by omega) (by omega) (by omega)
      smallFlipTarget_leaf6 smallFlipTarget_leaf7 smallFlipTarget_leaf8
      smallFlipTarget_meet_6_7 smallFlipTarget_meet_7_8
  intro P T FP FT
  exact hUniversal P FP T FT

/-- This explicit finite witness simultaneously satisfies
the first (all source flips into a fixed target) and second
(all target flips for a fixed source) requirements, with
the stronger cross-product of the two genuine flip orbits. -/
theorem exists_nine_vertex_target_absorbing_small_source_orbit :
    ∃ (B : Ordered3Graph Nat),
      FiniteRoleDiaryBlock B 9 ∧
      ∀ (P T : Ordered3Graph Nat),
        FiniteDiaryFlip smallFlipSource P 6 →
        FiniteDiaryFlip B T 9 →
        ∃ f : Nat → Nat,
          FiniteBoundedMeetEmbedding P T 6 9 f := by
  exact ⟨smallFlipTarget,smallFlipTarget_is_finiteDiary,
    smallFlipTarget_absorbs_entire_small_source_orbit⟩

end DiaryLeafPriority
end ThreeUniformDiaries
