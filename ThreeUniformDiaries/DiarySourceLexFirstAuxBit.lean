import ThreeUniformDiaries.DiarySourceLexAuxReduction

/-!
# The exact FIRST differing auxiliary bit at a proper singleton meet

Let the source singleton types of u,v meet at a proper earlier
level m. Type agreement below m gives equality of all earlier
singleton tests. Failure of agreement below m+1 forces an actual
disagreement at one of the NEW tests (q,m,u)/(q,m,v), q<m.

The mixed auxiliary meet of (m,u),(m,v) is precisely the first
such q. We prove q<m and actual disagreement at q, without using
source role axioms, S1/S2 or a target pre-diary. Coupled with the
previous full-mixed-meet calculation, this shows exactly which
SOURCE finite word bit determines the manuscript LexEarlier.
The remaining work is to relate this bit to binary numerical rank.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- A proper singleton meet m forces an earlier first differing
bit q<m in the mixed auxiliary column, and that disagreement
occurs at EXACTLY q = auxiliary meet, not merely at some test. -/
theorem onePass_source_mixedAux_first_difference
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hmu : m < u) (hmv : m < v)
    (hmeet : H.oneMeetLevel u v = m) :
    H.auxMeetLevel m u m v < m ∧
      ¬ (H.edge (H.auxMeetLevel m u m v) m u ↔
         H.edge (H.auxMeetLevel m u m v) m v) := by
  classical
  let q := H.auxMeetLevel m u m v
  have hCap : q ≤ m := by
    dsimp [q]
    simpa using (H.auxMeetLevel_le_min m u m v)
  have hOneBefore : H.SameOneTypeBelow m u v := by
    simpa only [hmeet] using (H.oneMeetLevel_agree u v)
  have hFailure : ¬ H.SameOneTypeBelow (m + 1) u v := by
    intro he
    have hBound : m + 1 ≤ min u v := by omega
    have hLe : m + 1 ≤ H.oneMeetLevel u v :=
      Nat.le_findGreatest hBound he
    rw [hmeet] at hLe
    omega
  have hAuxAgree : H.SameAuxTypeBelow q m u m v :=
    H.auxMeetLevel_agree m u m v
  have hQLt : q < m := by
    by_contra hNot
    have hEq : q = m := by omega
    have hNext : H.SameOneTypeBelow (m + 1) u v := by
      intro a b hab hb
      by_cases hPrev : b < m
      · exact hOneBefore hab hPrev
      · have hbm : b = m := by omega
        subst b
        exact hAuxAgree (by rw [hEq]; exact hab)
    exact hFailure hNext
  have hDiffAtQ : ¬ (H.edge q m u ↔ H.edge q m v) := by
    intro hEq
    have hNext : H.SameAuxTypeBelow (q + 1) m u m v := by
      intro a ha
      by_cases hPrev : a < q
      · exact hAuxAgree hPrev
      · have haq : a = q := by omega
        subst a
        exact hEq
    have hBound : q + 1 ≤ min m m := by omega
    have hLe : q + 1 ≤ H.auxMeetLevel m u m v :=
      Nat.le_findGreatest hBound hNext
    dsimp [q] at hLe
    omega
  exact ⟨hQLt, hDiffAtQ⟩

end DiaryLeafPriority
end ThreeUniformDiaries
