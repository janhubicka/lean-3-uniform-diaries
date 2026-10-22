import ThreeUniformDiaries.DiaryFiniteExplicitOppositeSmallSource
import ThreeUniformDiaries.DiaryFiniteE2E3CompleteCover
import ThreeUniformDiaries.DiaryFiniteFlipTransitivity
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex

/-!
# Exact classification of the six-vertex diary's genuine finite flips

The literal source has markers 0,1,2, a unique one-split 3,
and leaves 4,5. Its genuine flip preserves this role sequence
and the singleton meet 4 ∧ 5 = 3.

The E-only first-disagreement lemma forces the two possible
one-split incidences (0,3,4)/(0,3,5) to be OPPOSITE. By the
verified E2/E3 completeness theorem, all remaining incidences,
including the V3 leaf-pair marker, are uniquely determined.

Thus the entire genuine flip orbit consists EXACTLY of the
baseline positive-right source and its explicitly verified
negative-right flip. This is stronger than the Python count
of two: it is a proof for every bounded finite V/E/S diary
satisfying the literal flip definition, with no Boolean
independence assumptions and no additional axioms.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private theorem smallFlipSource_E2E3_shape
    (i j z : Fin 6)
    (h : IsFiniteFlipE2OrE3Edge
      smallFlipSource i.val j.val z.val) :
    i.val = 0 ∧ j.val = 3 ∧ (z.val = 4 ∨ z.val = 5) := by
  rcases h with ⟨hi,hj,hz⟩ | ⟨hi,_hj,_hz⟩
  · refine ⟨hi,smallFlipSource_oneSplit_eq_three hj,?_⟩
    exact (smallFlipSource_leaf_iff z.val hz.1 z.isLt).mp hz
  · exact False.elim (smallFlipSource_no_twoSplit i.val hi)

private theorem smallFlipSourceOpposite_E2E3_shape
    (i j z : Fin 6)
    (h : IsFiniteFlipE2OrE3Edge
      smallFlipSourceOpposite i.val j.val z.val) :
    i.val = 0 ∧ j.val = 3 ∧ (z.val = 4 ∨ z.val = 5) := by
  rcases h with ⟨hi,hj,hz⟩ | ⟨hi,_hj,_hz⟩
  · refine ⟨hi,smallFlipSourceOpposite_oneSplit_eq_three hj,?_⟩
    exact (smallFlipSourceOpposite_leaf_iff z.val hz.1 z.isLt).mp hz
  · exact False.elim (smallFlipSourceOpposite_no_twoSplit i.val hi)

/-- Every genuine finite diary flip of the six-vertex source
is literally either the source or its unique opposite
one-split orientation, including the forced V3 marker bit. -/
theorem smallFlipSource_all_flips_are_two
    {P : Ordered3Graph Nat}
    (F : FiniteDiaryFlip smallFlipSource P 6) :
    P = smallFlipSource ∨ P = smallFlipSourceOpposite := by
  have hs : IsOneSplit P 3 :=
    ((F.role_iff 3 smallFlipSource_oneSplit3.1 (by omega)).2.1).mp
      smallFlipSource_oneSplit3
  have hMeet : P.oneMeetLevel 4 5 = 3 :=
    (F.leaf_oneMeet 4 5 (by omega) (by omega)
      smallFlipSource_leaf4 smallFlipSource_leaf5).symm.trans
        smallFlipSource_leaf_meet
  have hOpposite :
      ¬ (P.edge 0 3 4 ↔ P.edge 0 3 5) :=
    E_oneSplit_distinguishing_zero_bit
      F.target_diary.prediary.permitted_edge
      3 4 5 hs (by omega) (by omega) hMeet
  by_cases hRight : P.edge 0 3 5
  · have hLeft : ¬ P.edge 0 3 4 := by
      intro h
      exact hOpposite (iff_of_true h hRight)
    left
    apply F.eq_of_E2E3_agreement
    intro i j z _hij _hjz hShape
    obtain ⟨hi,hj,hz⟩ :=
      smallFlipSource_E2E3_shape i j z hShape
    rcases hz with hz4 | hz5
    · simpa [hi,hj,hz4,smallFlipSource] using hLeft
    · simpa [hi,hj,hz5,smallFlipSource] using hRight
  · have hLeft : P.edge 0 3 4 := by
      by_contra h
      exact hOpposite (iff_of_false h hRight)
    right
    have F' : FiniteDiaryFlip smallFlipSourceOpposite P 6 :=
      smallFlipSourceOpposite_is_sourceFlip.symm.trans F
    apply F'.eq_of_E2E3_agreement
    intro i j z _hij _hjz hShape
    obtain ⟨hi,hj,hz⟩ :=
      smallFlipSourceOpposite_E2E3_shape i j z hShape
    rcases hz with hz4 | hz5
    · simpa [hi,hj,hz4,smallFlipSourceOpposite] using hLeft
    · simpa [hi,hj,hz5,smallFlipSourceOpposite] using hRight

/-- An EXACT characterisation of the genuine flip class,
not merely the assertion that at least two different flips
exist. The baseline and the opposite graph are the only
possible six-vertex flips, with each known to be a diary. -/
theorem smallFlipSource_flip_iff_two
    (P : Ordered3Graph Nat) :
    FiniteDiaryFlip smallFlipSource P 6 ↔
      P = smallFlipSource ∨ P = smallFlipSourceOpposite := by
  constructor
  · exact smallFlipSource_all_flips_are_two
  · rintro (rfl | rfl)
    · exact FiniteDiaryFlip.refl smallFlipSource_is_finiteDiary
    · exact smallFlipSourceOpposite_is_sourceFlip

end DiaryLeafPriority
end ThreeUniformDiaries
