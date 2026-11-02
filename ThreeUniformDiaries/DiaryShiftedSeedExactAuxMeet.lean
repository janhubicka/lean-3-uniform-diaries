import ThreeUniformDiaries.DiaryShiftedSeedAuxPrefix

/-!
# Track B: exact numerical auxiliary meet shift

For a valid original pair configuration (m,a),(m,b) with m<a,b,
the three-marker seed preserves the original last auxiliary type
agreement cut after adding three to the enumeration:
 auxMeet_S(m+3,a+3,m+3,b+3) = auxMeet_H(m,a,m,b)+3.

The lower bound is the checked shifted auxiliary-prefix lemma;
the upper bound is either the literal cap or a genuinely shifted
first disagreement of the original auxiliary type. We never infer
that an arbitrary type-respecting embedding preserves auxiliary
types. No diary assumptions or infinite source tail are used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

theorem shiftedDiarySeed_auxMeetLevel_exact
    (H : Ordered3Graph Nat) (m a b : Nat)
    (hma : m < a) (hmb : m < b)
    (hAB : H.SameOneTypeBelow m a b) :
    (shiftedDiarySeed H).auxMeetLevel
      (m+3) (a+3) (m+3) (b+3) =
      H.auxMeetLevel m a m b + 3 := by
  classical
  let S := shiftedDiarySeed H
  let q := H.auxMeetLevel m a m b
  have hq : q ≤ m := by
    have h := H.auxMeetLevel_le_min m a m b
    omega
  have hSrcAgree : H.SameAuxTypeBelow q m a m b :=
    H.auxMeetLevel_agree m a m b
  have hTargetAgree :
      S.SameAuxTypeBelow (q+3)
        (m+3) (a+3) (m+3) (b+3) :=
    shiftedDiarySeed_sameAuxTypeBelow_of_source
      H q m a b hma hmb hq hAB hSrcAgree
  have hLo : q+3 ≤ S.auxMeetLevel (m+3) (a+3) (m+3) (b+3) :=
    Nat.le_findGreatest (by omega) hTargetAgree
  have hHi :
      S.auxMeetLevel (m+3) (a+3) (m+3) (b+3) ≤ q+3 := by
    by_cases hCap : q = m
    · have hBound := S.auxMeetLevel_le_min
        (m+3) (a+3) (m+3) (b+3)
      omega
    · have hqStrict : q < m := by omega
      by_contra hn
      have hBeyond :
          q+4 ≤ S.auxMeetLevel (m+3) (a+3) (m+3) (b+3) := by
        omega
      have hTargetNext :
          S.SameAuxTypeBelow (q+4)
            (m+3) (a+3) (m+3) (b+3) := by
        have hagree := S.auxMeetLevel_agree
          (m+3) (a+3) (m+3) (b+3)
        intro x hx
        exact hagree (by omega)
      have hSrcNext : H.SameAuxTypeBelow (q+1) m a m b := by
        intro x hx
        have hShift : x+3 < q+4 := by omega
        have hNew := hTargetNext hShift
        have hEdgeA :=
          shiftedDiarySeed_leaf_edge_iff H x m a (by omega) hma
        have hEdgeB :=
          shiftedDiarySeed_leaf_edge_iff H x m b (by omega) hmb
        exact hEdgeA.symm.trans (hNew.trans hEdgeB)
      have hSourceBeyond : q+1 ≤ H.auxMeetLevel m a m b :=
        Nat.le_findGreatest (by omega) hSrcNext
      omega
  exact Nat.le_antisymm hHi hLo

end DiaryLeafPriority
end ThreeUniformDiaries
