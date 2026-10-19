import ThreeUniformDiaries.DiaryFiniteDummyTailCarrier

/-!
# Complete preservation of old finite types and meets under dummy tail

The dummy-leaf tail is appended strictly AFTER the finite source
frame. No new edge has its LAST vertex in the old finite prefix.
Therefore every singleton test ending at an old vertex, and every
auxiliary pair test with its last vertex old, is literally unchanged.

It follows at EVERY type cut, even cuts extending into the tail,
that all original finite singleton and full pair-type agreements
are preserved and reflected. The capped numerical singleton and
full ordered-pair meets of all finite source vertices are thus
identical in the infinite carrier, INCLUDING mixed split/leaf
pairs, diagonal and capped comparisons.

This is independent of the chosen cross marker bits and uses only
finite edge support. It establishes protection of the old picture
BEFORE verifying the countable V/E pre-diary or selecting V3 bits.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {n : Nat}

/-- Any two old finite vertices have identical singleton-prefix
agreement in H and in the infinite dummy-tail carrier, at ANY cut. -/
theorem finiteDummyTailCarrier_old_oneType_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (l u v : Nat) (hun : u < n) (hvn : v < n) :
    ((finiteDummyTailCarrier H n bits).SameOneTypeBelow l u v ↔
      H.SameOneTypeBelow l u v) := by
  constructor
  · intro ht a b hab hb
    have heU := finiteDummyTailCarrier_finite_edge_iff
      FH bits a b u hun
    have heV := finiteDummyTailCarrier_finite_edge_iff
      FH bits a b v hvn
    exact heU.symm.trans
      ((ht (a := a) (b := b) hab hb).trans heV)
  · intro hs a b hab hb
    have heU := finiteDummyTailCarrier_finite_edge_iff
      FH bits a b u hun
    have heV := finiteDummyTailCarrier_finite_edge_iff
      FH bits a b v hvn
    exact heU.trans
      ((hs (a := a) (b := b) hab hb).trans heV.symm)

/-- Any two old finite ordered pairs preserve their auxiliary
type at EVERY cut, even at cuts beyond the finite source. -/
theorem finiteDummyTailCarrier_old_auxType_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (l a b c d : Nat) (hbn : b < n) (hdn : d < n) :
    ((finiteDummyTailCarrier H n bits).SameAuxTypeBelow l a b c d ↔
      H.SameAuxTypeBelow l a b c d) := by
  constructor
  · intro ht x hx
    have heAB := finiteDummyTailCarrier_finite_edge_iff
      FH bits x a b hbn
    have heCD := finiteDummyTailCarrier_finite_edge_iff
      FH bits x c d hdn
    exact heAB.symm.trans ((ht (a := x) hx).trans heCD)
  · intro hs x hx
    have heAB := finiteDummyTailCarrier_finite_edge_iff
      FH bits x a b hbn
    have heCD := finiteDummyTailCarrier_finite_edge_iff
      FH bits x c d hdn
    exact heAB.trans ((hs (a := x) hx).trans heCD.symm)

/-- Full pair types of arbitrary old finite tuples are unchanged
at every cut, including both singleton-coordinate types. -/
theorem finiteDummyTailCarrier_old_twoType_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (l a b c d : Nat)
    (han : a < n) (hbn : b < n)
    (hcn : c < n) (hdn : d < n) :
    ((finiteDummyTailCarrier H n bits).SameTwoTypeBelow
        l a b c d ↔ H.SameTwoTypeBelow l a b c d) := by
  have hFirst := finiteDummyTailCarrier_old_oneType_iff
    FH bits l a c han hcn
  have hSecond := finiteDummyTailCarrier_old_oneType_iff
    FH bits l b d hbn hdn
  have hAux := finiteDummyTailCarrier_old_auxType_iff
    FH bits l a b c d hbn hdn
  exact and_congr hFirst (and_congr hSecond hAux)

/-- Exact NUMERIC singleton meet preservation for any two old
vertices; roles, equality and cap cases are unrestricted. -/
theorem finiteDummyTailCarrier_old_oneMeet_exact
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (u v : Nat) (hun : u < n) (hvn : v < n) :
    (finiteDummyTailCarrier H n bits).oneMeetLevel u v =
      H.oneMeetLevel u v := by
  classical
  let G := finiteDummyTailCarrier H n bits
  have hAtG : G.SameOneTypeBelow (G.oneMeetLevel u v) u v :=
    G.oneMeetLevel_agree u v
  have hAtH : H.SameOneTypeBelow (H.oneMeetLevel u v) u v :=
    H.oneMeetLevel_agree u v
  have hGSource : H.SameOneTypeBelow (G.oneMeetLevel u v) u v :=
    (finiteDummyTailCarrier_old_oneType_iff
      FH bits (G.oneMeetLevel u v) u v hun hvn).mp hAtG
  have hHSource : G.SameOneTypeBelow (H.oneMeetLevel u v) u v :=
    (finiteDummyTailCarrier_old_oneType_iff
      FH bits (H.oneMeetLevel u v) u v hun hvn).mpr hAtH
  have hGE : G.oneMeetLevel u v ≤ H.oneMeetLevel u v :=
    Nat.le_findGreatest (G.oneMeetLevel_le_min u v) hGSource
  have hHE : H.oneMeetLevel u v ≤ G.oneMeetLevel u v :=
    Nat.le_findGreatest (H.oneMeetLevel_le_min u v) hHSource
  change G.oneMeetLevel u v = H.oneMeetLevel u v
  omega

/-- Exact NUMERIC full two-meet preservation for any two ordered
pairs inside the old finite source (including mixed roles). -/
theorem finiteDummyTailCarrier_old_twoMeet_exact
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (a b c d : Nat)
    (han : a < n) (hbn : b < n)
    (hcn : c < n) (hdn : d < n) :
    (finiteDummyTailCarrier H n bits).twoMeetLevel a b c d =
      H.twoMeetLevel a b c d := by
  classical
  let G := finiteDummyTailCarrier H n bits
  have hAtG : G.SameTwoTypeBelow
      (G.twoMeetLevel a b c d) a b c d :=
    G.twoMeetLevel_agree a b c d
  have hAtH : H.SameTwoTypeBelow
      (H.twoMeetLevel a b c d) a b c d :=
    H.twoMeetLevel_agree a b c d
  have hGSource : H.SameTwoTypeBelow
      (G.twoMeetLevel a b c d) a b c d :=
    (finiteDummyTailCarrier_old_twoType_iff
      FH bits (G.twoMeetLevel a b c d) a b c d
      han hbn hcn hdn).mp hAtG
  have hHSource : G.SameTwoTypeBelow
      (H.twoMeetLevel a b c d) a b c d :=
    (finiteDummyTailCarrier_old_twoType_iff
      FH bits (H.twoMeetLevel a b c d) a b c d
      han hbn hcn hdn).mpr hAtH
  have hGE : G.twoMeetLevel a b c d ≤ H.twoMeetLevel a b c d :=
    Nat.le_findGreatest (G.twoMeetLevel_le_min a b c d) hGSource
  have hHE : H.twoMeetLevel a b c d ≤ G.twoMeetLevel a b c d :=
    Nat.le_findGreatest (H.twoMeetLevel_le_min a b c d) hHSource
  change G.twoMeetLevel a b c d = H.twoMeetLevel a b c d
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
