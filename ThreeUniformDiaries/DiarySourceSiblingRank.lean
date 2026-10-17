import ThreeUniformDiaries.DiarySourceLexBinaryRank
import ThreeUniformDiaries.DiaryLexEarlierComplement

/-!
# Rank order of distinct realised source children from one parent

The proper-meet source rank theorem is already proved directly
from first differing original singleton tests. Here we establish
the needed precondition for two distinct *normal* child germs:
equal parent codes but unequal genuine successor germs imply
their source singleton meet is EXACTLY the parent cut m.

We also handle terminal-vs-normal capped meets using the genuine
numerical definition of LexEarlier. Thus every pair of different
realised same-parent germs is ordered by their actual binary ranks
in exactly the manuscript's source LexEarlier sense. No target V3,
source S1/S2, or raw-code injectivity is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- Distinct realised normal singleton germs with a common
source parent have their first type divergence exactly at m. -/
theorem onePass_source_normalSiblings_meet_exact
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hmu : m < u) (hmv : m < v)
    (hParent : oneCode H m u = oneCode H m v)
    (hneq : oneGermCode H m u ≠ oneGermCode H m v) :
    H.oneMeetLevel u v = m := by
  classical
  have hAgree : H.SameOneTypeBelow m u v :=
    (oneCode_eq_iff_sameOneType H m u v).mp hParent
  have hLow : m ≤ H.oneMeetLevel u v :=
    Nat.le_findGreatest (by omega) hAgree
  have hNotNext : ¬ H.SameOneTypeBelow (m + 1) u v := by
    intro hs
    have hNextCode :
        oneCode H (m + 1) u = oneCode H (m + 1) v :=
      (oneCode_eq_iff_sameOneType H (m + 1) u v).mpr hs
    have huNe : u ≠ m := by omega
    have hvNe : v ≠ m := by omega
    have hEq : oneGermCode H m u = oneGermCode H m v := by
      simp [oneGermCode, huNe, hvNe, hParent, hNextCode]
    exact hneq hEq
  have hHigh : H.oneMeetLevel u v < m + 1 := by
    by_contra hn
    have hAgreeNext : H.SameOneTypeBelow (m + 1) u v := by
      intro a b hab hb
      exact (H.oneMeetLevel_agree u v) hab (by omega)
    exact hNotNext hAgreeNext
  omega

/-- If the source terminal vertex m and a later vertex share
their m-type, their singleton meet is precisely capped at m. -/
theorem onePass_source_terminalSibling_meet_exact
    (H : Ordered3Graph Nat) (m v : Nat) (hmv : m < v)
    (hParent : oneCode H m m = oneCode H m v) :
    H.oneMeetLevel m v = m := by
  classical
  have hAgree : H.SameOneTypeBelow m m v :=
    (oneCode_eq_iff_sameOneType H m m v).mp hParent
  have hLow : m ≤ H.oneMeetLevel m v :=
    Nat.le_findGreatest (by omega) hAgree
  have hHigh := H.oneMeetLevel_le_min m v
  omega

/-- Full realised-germ rank comparison, INCLUDING terminal
children. Only a common old parent code and unequal true
source germs are needed. -/
theorem onePass_source_siblingGermRank_lt_iff_lex
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hParent : oneCode H m u = oneCode H m v)
    (hneq : oneGermCode H m u ≠ oneGermCode H m v) :
    (oneGermBinaryRank m (oneGermCode H m u) <
      oneGermBinaryRank m (oneGermCode H m v)) ↔
        LexEarlier H u v := by
  by_cases hu : u = m
  · subst u
    by_cases hv : v = m
    · subst v
      exact False.elim (hneq rfl)
    · have hmv' : m < v := by omega
      have hMeet :=
        onePass_source_terminalSibling_meet_exact H m v hmv' hParent
      have hLex : LexEarlier H m v :=
        Or.inl ⟨hmv', hMeet⟩
      have hRank0 := terminal_oneGerm_rank_zero H m
      have hRankPos :=
        normal_oneGerm_rank_pos H m v (by omega)
      have hRank :
          oneGermBinaryRank m (oneGermCode H m m) <
            oneGermBinaryRank m (oneGermCode H m v) := by
        rw [hRank0]
        exact hRankPos
      exact iff_of_true hRank hLex
  · have hmu' : m < u := by omega
    by_cases hv : v = m
    · subst v
      have hMeet :=
        onePass_source_terminalSibling_meet_exact
          H m u hmu' hParent.symm
      have hLex : LexEarlier H m u := Or.inl ⟨hmu', hMeet⟩
      have hNotLex : ¬ LexEarlier H u m :=
        (lexEarlier_swap_complement H m u (by omega)).mp hLex
      have hRank0 := terminal_oneGerm_rank_zero H m
      have hRankPos :=
        normal_oneGerm_rank_pos H m u (by omega)
      have hNotRank :
          ¬ (oneGermBinaryRank m (oneGermCode H m u) <
            oneGermBinaryRank m (oneGermCode H m m)) := by
        rw [hRank0]
        omega
      exact iff_of_false hNotRank hNotLex
    · have hmv' : m < v := by omega
      have hMeet :=
        onePass_source_normalSiblings_meet_exact H m u v
          hmu' hmv' hParent hneq
      exact onePass_source_normalGermRank_lt_iff_lex H m u v
        hmu' hmv' hMeet

end DiaryLeafPriority
end ThreeUniformDiaries
