import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex

/-!
# Two 1-split flip choices are NOT independent

In the nine-vertex three-leaf diary from the explicit
shared-2-split obstruction, the leaf singleton meets are
5 wedge 7 = 4 and 7 wedge 8 = 6, and the full ordered-pair
meet of (5,7) and (7,8) is 3.

These numerical meets force the right positive branch bits
at 1-splits 4 and 6 to be EQUAL in every flip. Indeed the
full pair meet being at least 2 forces the two marker-one
auxiliary incidences (1,5,7) and (1,7,8) to agree. V3 and
the verified E-only right-split lexicographic formula identify
these two marker bits with E(0,4,7) and E(0,6,8).

This is a nontrivial geometric obstruction to treating
all active diary split choices as a FREE Boolean cube. It
does not refute the every-target-flip absorption theorem,
but it means an unrestricted bit-by-bit correction recursion
may demand a source flip which does not exist.

All statements are implications from genuine FINITE V/E/S
diary hypotheses. No explicit nine-vertex diary certificate
or unsupported mixed-meet preservation is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A full pair meet surviving beyond marker 1 couples the
Devlin comparisons of its two ordered leaf pairs. Here the
singleton meets of (5,7) and (7,8) are at one-splits 4 and 6,
so their positive branch choices are necessarily identical. -/
theorem finiteDiary_two_oneSplit_bits_coupled
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n) (hn : 9 ≤ n)
    (h5 : IsLeaf H 5) (h7 : IsLeaf H 7)
    (h8 : IsLeaf H 8)
    (h57 : H.oneMeetLevel 5 7 = 4)
    (h78 : H.oneMeetLevel 7 8 = 6)
    (hPair : 2 ≤ H.twoMeetLevel 5 7 7 8) :
    (H.edge 0 4 7 ↔ H.edge 0 6 8) := by
  have h4 : IsOneSplit H 4 := by
    rw [← h57]
    exact D.singleton_meets 5 7 (by omega) (by omega) h5 h7
  have h6 : IsOneSplit H 6 := by
    rw [← h78]
    exact D.singleton_meets 7 8 (by omega) (by omega) h7 h8
  have hLex57 : LexEarlier H 5 7 ↔ H.edge 0 4 7 :=
    E_oneSplit_lexEarlier_iff_right
      D.prediary.permitted_edge 4 5 7 h4
      (by omega) (by omega) h57
  have hLex78 : LexEarlier H 7 8 ↔ H.edge 0 6 8 :=
    E_oneSplit_lexEarlier_iff_right
      D.prediary.permitted_edge 6 7 8 h6
      (by omega) (by omega) h78
  have hMark57 : H.edge 1 5 7 ↔ LexEarlier H 5 7 :=
    D.prediary.leaf_marker_one 5 7 (by omega) (by omega) h5 h7
  have hMark78 : H.edge 1 7 8 ↔ LexEarlier H 7 8 :=
    D.prediary.leaf_marker_one 7 8 (by omega) (by omega) h7 h8
  have hAux : H.edge 1 5 7 ↔ H.edge 1 7 8 :=
    (H.twoMeetLevel_agree 5 7 7 8).2.2 (by omega)
  exact hLex57.symm.trans
    (hMark57.symm.trans
      (hAux.trans (hMark78.trans hLex78)))

/-- Consequently all genuine flips of a finite source diary
with the displayed three-leaf meet pattern must synchronize
the branch choice at source one-splits 4 and 6. In particular,
no valid flip can toggle exactly one of them. -/
theorem finiteDiaryFlip_two_oneSplit_bits_coupled
    {A B : Ordered3Graph Nat}
    (F : FiniteDiaryFlip A B 9)
    (h5 : IsLeaf A 5) (h7 : IsLeaf A 7)
    (h8 : IsLeaf A 8)
    (h57 : A.oneMeetLevel 5 7 = 4)
    (h78 : A.oneMeetLevel 7 8 = 6)
    (hPair : A.twoMeetLevel 5 7 7 8 = 3) :
    (B.edge 0 4 7 ↔ B.edge 0 6 8) := by
  have hB5 : IsLeaf B 5 :=
    ((F.role_iff 5 (by omega) (by omega)).1).mp h5
  have hB7 : IsLeaf B 7 :=
    ((F.role_iff 7 (by omega) (by omega)).1).mp h7
  have hB8 : IsLeaf B 8 :=
    ((F.role_iff 8 (by omega) (by omega)).1).mp h8
  have hB57 : B.oneMeetLevel 5 7 = 4 :=
    (F.leaf_oneMeet 5 7 (by omega) (by omega) h5 h7).symm.trans h57
  have hB78 : B.oneMeetLevel 7 8 = 6 :=
    (F.leaf_oneMeet 7 8 (by omega) (by omega) h7 h8).symm.trans h78
  have hBPair : B.twoMeetLevel 5 7 7 8 = 3 :=
    (F.leaf_twoMeet 5 7 7 8 (by omega) (by omega)
      (by omega) (by omega) h5 h7 h7 h8).symm.trans hPair
  exact finiteDiary_two_oneSplit_bits_coupled
    F.target_diary (by omega) hB5 hB7 hB8
    hB57 hB78 (by omega)

/-- The two independently suggested flip changes cannot be
made with opposite truth values in an actual finite diary
preserving the nine-vertex source leaf meet data. -/
theorem finiteDiaryFlip_no_independent_two_oneSplit_bits
    {A B : Ordered3Graph Nat}
    (F : FiniteDiaryFlip A B 9)
    (h5 : IsLeaf A 5) (h7 : IsLeaf A 7)
    (h8 : IsLeaf A 8)
    (h57 : A.oneMeetLevel 5 7 = 4)
    (h78 : A.oneMeetLevel 7 8 = 6)
    (hPair : A.twoMeetLevel 5 7 7 8 = 3) :
    ¬ ((B.edge 0 4 7 ∧ ¬ B.edge 0 6 8) ∨
      (¬ B.edge 0 4 7 ∧ B.edge 0 6 8)) := by
  have hCoupled :=
    finiteDiaryFlip_two_oneSplit_bits_coupled F
      h5 h7 h8 h57 h78 hPair
  tauto

end DiaryLeafPriority
end ThreeUniformDiaries
