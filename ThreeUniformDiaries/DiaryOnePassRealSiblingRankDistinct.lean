import ThreeUniformDiaries.DiarySourceSiblingRank

/-!
# Strict separation of numerical ranks for genuine sibling germs

The binary rank deliberately ignores invalid coordinates of raw finite
Boolean functions; rank injectivity on arbitrary code-space values is
false. However two DIFFERENT oneGermCode values of actual source
vertices with the same old one-type parent have distinct ranks.

The proof reuses the checked source sibling rank/LexEarlier
equivalence in BOTH directions together with the literal
LexEarlier reversal lemma. No normalisation axiom, source S1/S2,
or target pre-diary assertion is introduced.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Distinct genuine same-parent singleton germs have unequal ranks.
The theorem is intentionally limited to real source vertex codes. -/
theorem onePass_realSiblingGerm_ranks_ne
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hParent : oneCode H m u = oneCode H m v)
    (hNe : oneGermCode H m u ≠ oneGermCode H m v) :
    oneGermBinaryRank m (oneGermCode H m u) ≠
      oneGermBinaryRank m (oneGermCode H m v) := by
  have huv : u ≠ v := by
    intro heq
    subst v
    exact hNe rfl
  by_cases hLex : LexEarlier H u v
  · have hRank :=
      (onePass_source_siblingGermRank_lt_iff_lex
        H m u v hmu hmv hParent hNe).mpr hLex
    omega
  · have hReverse : LexEarlier H v u :=
      (lexEarlier_swap_complement H v u huv.symm).mpr hLex
    have hRank :=
      (onePass_source_siblingGermRank_lt_iff_lex
        H m v u hmv hmu hParent.symm hNe.symm).mpr hReverse
    omega

/-- The weak rank inequality for real siblings is strict as soon as
their true source germs are unequal. -/
theorem onePass_realSiblingGerm_rank_lt_of_le
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hParent : oneCode H m u = oneCode H m v)
    (hNe : oneGermCode H m u ≠ oneGermCode H m v)
    (hLe : oneGermBinaryRank m (oneGermCode H m v) ≤
           oneGermBinaryRank m (oneGermCode H m u)) :
    oneGermBinaryRank m (oneGermCode H m v) <
      oneGermBinaryRank m (oneGermCode H m u) := by
  have hDifferent :=
    onePass_realSiblingGerm_ranks_ne H m u v hmu hmv hParent hNe
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
