import ThreeUniformDiaries.DiaryOnePassSourceColumnTests
import ThreeUniformDiaries.DiaryOnePassFirstBitRank
import ThreeUniformDiaries.DiarySourceLexFirstAuxBit

/-!
# First source singleton difference determines actual binary germ rank

At a proper original singleton meet m of u and v, the source
finite singleton words have identical prefixes below m, and their
new m-column words first differ at the mixed auxiliary meet q<m.
The literal paper's LexEarlier reads the right edge (q,m,v).
General binary numeral arithmetic and the *genuine* source-code
column decomposition now prove that the source next-cut binary
rank inequality has exactly this orientation.

This uses no source S1/S2 and no postulated output V3 condition.
It does not pretend that raw unnormalised finite functions have
injective binary numerals.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- When two genuine source singleton types have first proper
meet m, numerical next-cut code rank comparison is equivalent
to the manuscript's literal LexEarlier relation on those leaves.
No diary axioms are needed. -/
theorem onePass_source_nextCodeRank_lt_iff_lex
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hmu : m < u) (hmv : m < v)
    (hmeet : H.oneMeetLevel u v = m) :
    (oneCodeBinaryRank (m + 1) (oneCode H (m + 1) u) <
      oneCodeBinaryRank (m + 1) (oneCode H (m + 1) v)) ↔
        LexEarlier H u v := by
  classical
  let q := H.auxMeetLevel m u m v
  obtain ⟨hq,hDiff⟩ :=
    onePass_source_mixedAux_first_difference H m u v hmu hmv hmeet
  have hOld : H.SameOneTypeBelow m u v := by
    simpa only [hmeet] using (H.oneMeetLevel_agree u v)
  have hPrefix :=
    onePass_source_prefix_word_eq H m u v hOld
  have hColLen : (onePassSourceColumn H m u).length =
      (onePassSourceColumn H m v).length := by
    simp [onePassSourceColumn]
  have hQLen : q < (onePassSourceColumn H m u).length := by
    simpa [onePassSourceColumn] using hq
  have hAuxAgree : H.SameAuxTypeBelow q m u m v :=
    H.auxMeetLevel_agree m u m v
  have hColBefore :
      ∀ i : Nat, i < q →
        (onePassSourceColumn H m u)[i]? =
          (onePassSourceColumn H m v)[i]? :=
    onePass_sourceColumn_agree_before H m u v q hq.le hAuxAgree
  have hColumnRank :
      (binaryWordRank (onePassSourceColumn H m u) <
        binaryWordRank (onePassSourceColumn H m v)) ↔
          H.edge q m v := by
    by_cases hv : H.edge q m v
    · have hu : ¬ H.edge q m u := by
        intro hp
        exact hDiff (iff_of_true hp hv)
      have hx : (onePassSourceColumn H m u)[q]? = some false :=
        (onePass_sourceColumn_false_iff H m u q hq).mpr hu
      have hy : (onePassSourceColumn H m v)[q]? = some true :=
        (onePass_sourceColumn_true_iff H m v q hq).mpr hv
      have hlt := onePass_binaryRank_lt_of_first_bit
        (onePassSourceColumn H m u)
        (onePassSourceColumn H m v)
        hColLen q hQLen hColBefore hx hy
      exact iff_of_true hlt hv
    · have hu : H.edge q m u := by
        by_contra hNo
        exact hDiff (iff_of_false hNo hv)
      have hx : (onePassSourceColumn H m u)[q]? = some true :=
        (onePass_sourceColumn_true_iff H m u q hq).mpr hu
      have hy : (onePassSourceColumn H m v)[q]? = some false :=
        (onePass_sourceColumn_false_iff H m v q hq).mpr hv
      have hgt := onePass_binaryRank_gt_of_first_bit
        (onePassSourceColumn H m u)
        (onePassSourceColumn H m v)
        hColLen q hQLen hColBefore hx hy
      have hNot :
          ¬ (binaryWordRank (onePassSourceColumn H m u) <
            binaryWordRank (onePassSourceColumn H m v)) := by
        omega
      exact iff_of_false hNot hv
  have hFullRank :
      (oneCodeBinaryRank (m + 1) (oneCode H (m + 1) u) <
        oneCodeBinaryRank (m + 1) (oneCode H (m + 1) v)) ↔
      (binaryWordRank (onePassSourceColumn H m u) <
        binaryWordRank (onePassSourceColumn H m v)) := by
    rw [oneCodeBinaryRank_eq_word, oneCodeBinaryRank_eq_word,
      onePass_oneCodeBitWord_succ_original H m u,
      onePass_oneCodeBitWord_succ_original H m v,
      onePass_binaryRank_append, onePass_binaryRank_append,
      hPrefix, hColLen]
    omega
  exact hFullRank.trans
    (hColumnRank.trans
      (onePass_lexEarlier_iff_mixedAux_right
        H m u v hmu hmv hmeet).symm)

/-- The equivalent statement for the actual realised, normal
source singleton germs at their first proper singleton meet. -/
theorem onePass_source_normalGermRank_lt_iff_lex
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hmu : m < u) (hmv : m < v)
    (hmeet : H.oneMeetLevel u v = m) :
    (oneGermBinaryRank m (oneGermCode H m u) <
      oneGermBinaryRank m (oneGermCode H m v)) ↔
        LexEarlier H u v := by
  have hu : u ≠ m := by omega
  have hv : v ≠ m := by omega
  simpa [oneGermBinaryRank, oneGermCode, hu, hv] using
    onePass_source_nextCodeRank_lt_iff_lex
      H m u v hmu hmv hmeet

end DiaryLeafPriority
end ThreeUniformDiaries
