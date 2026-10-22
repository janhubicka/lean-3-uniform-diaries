import ThreeUniformDiaries.DiaryFiniteThreeLeafAlternation
import ThreeUniformDiaries.DiaryFiniteThreePairAlternation

/-!
# The outer vertices of alternating split witnesses agree past the split

The E2 three-leaf and E3 three-pair gadgets are not merely
Boolean 010/101 patterns: the two outer objects have the SAME
bit at the intervening split, and their earlier types agree.

At a one-split s, if a^b=b^c=s then the OUTER leaf singleton
meet a^c is strictly greater than s.

At a two-split s, if the full meets p^q=q^r=s for three
ordered pairs, then their outer full meet p^r is strictly
greater than s. The sole possible new auxiliary test at s
has the same value on both outer pairs, while all singleton
tests with middle vertex s are forbidden by E1--E5.

These facts explain why the positive outer objects form a
V1/V2-compatible common type class. They do NOT suffice for
the global cross-copy early-leaf coherence or flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The two outer leaves have their first singleton type
disagreement strictly AFTER the intervening one-split. -/
theorem finite_three_leaf_outer_oneMeet_gt
    {H : Ordered3Graph Nat} {k : Nat}
    (D : FiniteRolePrediaryBlock H k)
    (s a b c : Nat)
    (hs : IsOneSplit H s)
    (hsa : s < a) (hab : a < b) (hbc : b < c)
    (hmAB : H.oneMeetLevel a b = s)
    (hmBC : H.oneMeetLevel b c = s) :
    s < H.oneMeetLevel a c := by
  classical
  have hAB : H.SameOneTypeBelow s a b := by
    rw [← hmAB]
    exact H.oneMeetLevel_agree a b
  have hBC : H.SameOneTypeBelow s b c := by
    rw [← hmBC]
    exact H.oneMeetLevel_agree b c
  have hBefore : H.SameOneTypeBelow s a c := by
    intro x y hxy hy
    exact (hAB hxy hy).trans (hBC hxy hy)
  have hDiffAB : ¬ (H.edge 0 s a ↔ H.edge 0 s b) :=
    E_oneSplit_distinguishing_zero_bit D.permitted_edge
      s a b hs hab hsa hmAB
  have hDiffBC : ¬ (H.edge 0 s b ↔ H.edge 0 s c) :=
    E_oneSplit_distinguishing_zero_bit D.permitted_edge
      s b c hs hbc (by omega) hmBC
  have hOuterBit : H.edge 0 s a ↔ H.edge 0 s c := by
    tauto
  have hNext : H.SameOneTypeBelow (s + 1) a c := by
    apply (H.sameOneTypeBelow_succ_iff s a c).mpr
    refine ⟨hBefore,?_⟩
    intro x hx
    by_cases hzero : x = 0
    · subst x
      exact hOuterBit
    · have hxpos : 0 < x := by omega
      exact iff_of_false
        (E_oneSplit_no_positive_aux D.permitted_edge s x a hs hxpos)
        (E_oneSplit_no_positive_aux D.permitted_edge s x c hs hxpos)
  have hBound : s + 1 ≤ min a c := by omega
  have hAfter : s + 1 ≤ H.oneMeetLevel a c :=
    Nat.le_findGreatest hBound hNext
  omega

/-- The two outer ordered leaf pairs have their full type
meet strictly AFTER the intervening two-split, as required
for a coherent positive V2 class. -/
theorem finite_three_pair_outer_twoMeet_gt
    {H : Ordered3Graph Nat} {k : Nat}
    (D : FiniteRolePrediaryBlock H k)
    (s a b c d e f : Nat)
    (hs : IsTwoSplit H s)
    (hsa : s < a) (hsc : s < c) (hse : s < e)
    (hab : a < b) (hcd : c < d) (hef : e < f)
    (hMeet01 : H.twoMeetLevel a b c d = s)
    (hMeet12 : H.twoMeetLevel c d e f = s) :
    s < H.twoMeetLevel a b e f := by
  classical
  have hPQ : H.SameTwoTypeBelow s a b c d := by
    rw [← hMeet01]
    exact H.twoMeetLevel_agree a b c d
  have hQR : H.SameTwoTypeBelow s c d e f := by
    rw [← hMeet12]
    exact H.twoMeetLevel_agree c d e f
  have hBefore : H.SameTwoTypeBelow s a b e f := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      exact (hPQ.1 hxy hy).trans (hQR.1 hxy hy)
    · intro x y hxy hy
      exact (hPQ.2.1 hxy hy).trans (hQR.2.1 hxy hy)
    · intro x hx
      exact (hPQ.2.2 hx).trans (hQR.2.2 hx)
  have hDiffPQ : ¬ (H.edge s a b ↔ H.edge s c d) :=
    E_twoSplit_pair_aux_distinguishes D.permitted_edge
      s a b c d hs hsa hsc hMeet01
  have hDiffQR : ¬ (H.edge s c d ↔ H.edge s e f) :=
    E_twoSplit_pair_aux_distinguishes D.permitted_edge
      s c d e f hs hsc hse hMeet12
  have hOuterBit : H.edge s a b ↔ H.edge s e f := by
    tauto
  have hNext : H.SameTwoTypeBelow (s + 1) a b e f := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      by_cases hbefore : y < s
      · exact hBefore.1 hxy hbefore
      · have hys : y = s := by omega
        subst y
        exact iff_of_false
          (E_twoSplit_no_incoming_middle D.permitted_edge s x a hs)
          (E_twoSplit_no_incoming_middle D.permitted_edge s x e hs)
    · intro x y hxy hy
      by_cases hbefore : y < s
      · exact hBefore.2.1 hxy hbefore
      · have hys : y = s := by omega
        subst y
        exact iff_of_false
          (E_twoSplit_no_incoming_middle D.permitted_edge s x b hs)
          (E_twoSplit_no_incoming_middle D.permitted_edge s x f hs)
    · intro x hx
      by_cases hbefore : x < s
      · exact hBefore.2.2 hbefore
      · have hxs : x = s := by omega
        subst x
        exact hOuterBit
  have hBound : s + 1 ≤ min a e := by omega
  have hAfter : s + 1 ≤ H.twoMeetLevel a b e f :=
    Nat.le_findGreatest hBound hNext
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
