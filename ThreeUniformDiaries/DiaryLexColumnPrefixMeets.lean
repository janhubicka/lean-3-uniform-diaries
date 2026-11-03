import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Track B: common singleton prefix preserves comparison with earlier columns

The outstanding shifted-seed V3 lemma needs only finite
*column* invariance: if a and b have the same singleton type below
m, then an earlier source vertex t <= m sees identical singleton
and two-type meet levels when compared with a and b.

These elementary identities are for an ARBITRARY enumerated
3-hypergraph, without diary axioms or any generic embedding.
They isolate the numerical input needed for the seed LexEarlier
argument, without incorrectly treating its new marker edges as
invisible or using the false prediary old-cut transfer.

Only genuine tests below the specified cuts are used. This file
does not yet prove the final shifted LexEarlier identity.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- If a,b have exactly the same singleton type below m, the
numerical singleton meet of an earlier t with a or b is identical.
All test coordinates witnessing either meet lie below t <= m. -/
theorem oneMeetLevel_eq_of_common_one_prefix
    (H : Ordered3Graph Nat)
    (m t a b : Nat)
    (hAB : H.SameOneTypeBelow m a b)
    (htm : t ≤ m) (hta : t ≤ a) (htb : t ≤ b) :
    H.oneMeetLevel t a = H.oneMeetLevel t b := by
  classical
  apply Nat.le_antisymm
  · have hqBound := H.oneMeetLevel_le_min t a
    have hqMax : H.oneMeetLevel t a ≤ min t b := by omega
    apply Nat.le_findGreatest hqMax
    intro x y hxy hy
    have hOne := H.oneMeetLevel_agree t a
    have hTA := hOne hxy hy
    have hABxy := hAB hxy (by omega)
    exact hTA.trans hABxy
  · have hqBound := H.oneMeetLevel_le_min t b
    have hqMax : H.oneMeetLevel t b ≤ min t a := by omega
    apply Nat.le_findGreatest hqMax
    intro x y hxy hy
    have hOne := H.oneMeetLevel_agree t b
    have hTB := hOne hxy hy
    have hABxy := hAB hxy (by omega)
    exact hTB.trans hABxy.symm

/-- The auxiliary meet between (r,t) and (r,a) does not change
when a is replaced by b, provided a,b have identical singleton
tests strictly through the middle-coordinate r.

In particular r < m ensures every comparison test x<r is
already included in the supplied singleton prefix agreement. -/
theorem auxMeetLevel_eq_of_common_one_prefix
    (H : Ordered3Graph Nat)
    (m r t a b : Nat)
    (hAB : H.SameOneTypeBelow m a b)
    (hrm : r < m) :
    H.auxMeetLevel r t r a = H.auxMeetLevel r t r b := by
  classical
  apply Nat.le_antisymm
  · have hqBound := H.auxMeetLevel_le_min r t r a
    have hqMax : H.auxMeetLevel r t r a ≤ min r r := hqBound
    apply Nat.le_findGreatest hqMax
    intro x hx
    have hAux := H.auxMeetLevel_agree r t r a
    have hTA := hAux hx
    have hABxr := hAB (a := x) (b := r) (by omega) (by omega)
    exact hTA.trans hABxr
  · have hqBound := H.auxMeetLevel_le_min r t r b
    have hqMax : H.auxMeetLevel r t r b ≤ min r r := hqBound
    apply Nat.le_findGreatest hqMax
    intro x hx
    have hAux := H.auxMeetLevel_agree r t r b
    have hTB := hAux hx
    have hABxr := hAB (a := x) (b := r) (by omega) (by omega)
    exact hTB.trans hABxr.symm

/-- At a proper comparison column r<t, the corresponding
ordinary full pair-meets are equal under replacement of the
right endpoint by another vertex with the same prefix.

This is the numerical ingredient behind invariance of
LexEarlier(t,a) under replacing a by b. -/
theorem twoMeetLevel_eq_of_common_one_prefix
    (H : Ordered3Graph Nat)
    (m r t a b : Nat)
    (hAB : H.SameOneTypeBelow m a b)
    (htm : t ≤ m) (hrm : r < m)
    (hrt : r < t) (hra : r < a) (hrb : r < b)
    (hta : t ≤ a) (htb : t ≤ b) :
    H.twoMeetLevel r t r a = H.twoMeetLevel r t r b := by
  have hOne := H.oneMeetLevel_eq_of_common_one_prefix
    m t a b hAB htm hta htb
  have hAux := H.auxMeetLevel_eq_of_common_one_prefix
    m r t a b hAB hrm
  calc
    H.twoMeetLevel r t r a =
        min (H.auxMeetLevel r t r a)
          (min (H.oneMeetLevel r r) (H.oneMeetLevel t a)) :=
      H.twoMeetLevel_eq_min r t r a hrt hra
    _ = min (H.auxMeetLevel r t r b)
          (min (H.oneMeetLevel r r) (H.oneMeetLevel t b)) := by
      rw [hAux, hOne]
    _ = H.twoMeetLevel r t r b :=
      (H.twoMeetLevel_eq_min r t r b hrt hrb).symm

end Ordered3Graph
end ThreeUniformDiaries
