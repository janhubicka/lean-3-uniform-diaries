import ThreeUniformDiaries.DiaryFiniteThreeTailOverlapProfiles
import ThreeUniformDiaries.DiaryOrientationCalibrationTriple
import ThreeUniformDiaries.DiaryEmbeddingExactOneMeets

/-!
# The four-tail edge amalgam contains a genuine calibration triple

Two three-tail pictures can be glued along their common protected
prefix, split, and positive central leaf. The first picture has
vertices (split, negative leaf, positive leaf), the second has
(split, positive leaf, negative leaf). The resulting ordered
four-tail picture has vertices n,n+1,n+2,n+3, of which the last
three form a calibration triple with singleton meet n.

The required source hypotheses are transparent:
* A and B agree on their shared n+2-vertex overlap;
* the first two leaves of A share their singleton type below n;
* those two leaves are distinguished by an edge (z,n,_) with z<n;
* the negative leaf of A and the negative leaf of B have equal
  singleton prefix profiles and equal split-incidence profiles.

No target type equality across omitted enumeration levels is
assumed. The four-tail source is the actual finite EDGE amalgam.
What remains is to realise the corresponding selected ATR
finite-pointed source codes in a common generic copy.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The negative leaves of two compatible three-tail pictures
retain the same singleton type through the SHARED split's
successor cut in the four-tail free amalgam. -/
theorem threeTailFreeAmalgam_negative_sameOneType
    (A B : Ordered3Graph Nat) (n : Nat)
    (hOverlap : ThreeTailOverlapCompatible A B n)
    (hNegativePrefix :
      ∀ x y, x < y → y < n →
        (A.edge x y (n+1) ↔ B.edge x y (n+2)))
    (hNegativeSplit :
      ∀ x, x < n →
        (A.edge x n (n+1) ↔ B.edge x n (n+2))) :
    (threeTailFreeAmalgam A B n).SameOneTypeBelow
      (n+1) (n+1) (n+3) := by
  let C := threeTailFreeAmalgam A B n
  intro x y hxy hy
  have hyN : y ≤ n := by omega
  have hxN : x ≤ n := by omega
  have hOld :
      C.edge x y (n+1) ↔ A.edge x y (n+1) :=
    threeTailFreeAmalgam_left A B n x y (n+1) (by omega)
  have hNew :
      C.edge x y (n+3) ↔ B.edge x y (n+2) := by
    have hr := threeTailFreeAmalgam_right
      A B n hOverlap x y (n+2) hxy (by omega) (by omega)
    simpa only [threeTailShift_prefix n x hxN,
      threeTailShift_prefix n y hyN,
      threeTailShift_secondLeaf n] using hr
  rcases lt_or_eq_of_le hyN with hyLt | hyEq
  · exact hOld.trans
      ((hNegativePrefix x y hxy hyLt).trans hNew.symm)
  · subst y
    exact hOld.trans
      ((hNegativeSplit x (by omega)).trans hNew.symm)

/-- The split n remains the EXACT singleton meet of the first
and central leaves of the free amalgam. This is established by
the complete prefix type agreement and a real disagreement at
the split, not by assuming global preservation of type meets. -/
theorem threeTailFreeAmalgam_first_meet
    (A B : Ordered3Graph Nat) (n : Nat) (hn : 0 < n)
    (hSame : A.SameOneTypeBelow n (n+1) (n+2))
    (hSplit : ¬ (A.edge 0 n (n+1) ↔ A.edge 0 n (n+2))) :
    (threeTailFreeAmalgam A B n).oneMeetLevel
      (n+1) (n+2) = n := by
  let C := threeTailFreeAmalgam A B n
  have hSameC : C.SameOneTypeBelow n (n+1) (n+2) := by
    intro x y hxy hy
    have hL : C.edge x y (n+1) ↔ A.edge x y (n+1) :=
      threeTailFreeAmalgam_left A B n x y (n+1) (by omega)
    have hR : C.edge x y (n+2) ↔ A.edge x y (n+2) :=
      threeTailFreeAmalgam_left A B n x y (n+2) (by omega)
    exact hL.trans ((hSame hxy hy).trans hR.symm)
  have hLower : n ≤ C.oneMeetLevel (n+1) (n+2) :=
    Nat.le_findGreatest (by omega) hSameC
  have hDiff : ¬ (C.edge 0 n (n+1) ↔
      C.edge 0 n (n+2)) := by
    intro heq
    have hL : C.edge 0 n (n+1) ↔ A.edge 0 n (n+1) :=
      threeTailFreeAmalgam_left A B n 0 n (n+1) (by omega)
    have hR : C.edge 0 n (n+2) ↔ A.edge 0 n (n+2) :=
      threeTailFreeAmalgam_left A B n 0 n (n+2) (by omega)
    exact hSplit (hL.symm.trans (heq.trans hR))
  have hUpper : C.oneMeetLevel (n+1) (n+2) ≤ n :=
    C.oneMeetLevel_le_of_edge_disagreement
      (n+1) (n+2) 0 n hn hDiff
  exact Nat.le_antisymm hUpper hLower

/-- The actual four-tail amalgam has the calibration triple
n < n+1 < n+2 < n+3. All proper one-type requirements are
consequences of the four explicit finite edge profiles. -/
def threeTailFreeAmalgam_calibrationTriple
    (A B : Ordered3Graph Nat) (n : Nat) (hn : 0 < n)
    (hOverlap : ThreeTailOverlapCompatible A B n)
    (hSame : A.SameOneTypeBelow n (n+1) (n+2))
    (hSplit : ¬ (A.edge 0 n (n+1) ↔
      A.edge 0 n (n+2)))
    (hNegativePrefix :
      ∀ x y, x < y → y < n →
        (A.edge x y (n+1) ↔ B.edge x y (n+2)))
    (hNegativeSplit :
      ∀ x, x < n →
        (A.edge x n (n+1) ↔ B.edge x n (n+2))) :
    OrientationCalibrationTriple (threeTailFreeAmalgam A B n) := by
  refine {
    m := n
    a := n+1
    b := n+2
    c := n+3
    m_lt_a := by omega
    a_lt_b := by omega
    b_lt_c := by omega
    meet_ab := ?_
    same_ac := ?_
  }
  · exact threeTailFreeAmalgam_first_meet A B n hn hSame hSplit
  · exact threeTailFreeAmalgam_negative_sameOneType
      A B n hOverlap hNegativePrefix hNegativeSplit

end Ordered3Graph
end ThreeUniformDiaries
