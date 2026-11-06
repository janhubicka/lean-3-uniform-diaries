import ThreeUniformDiaries.DiaryMarkerFixedPositivePairTypes
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Track B: exact numerical meets protected by chronological marker columns

New cross-branch marker edges always have first vertex 1 or 2.
Consequently every edge with first vertex 0, including all role
markers and genuine singleton split-witness bits, is unchanged.

A pair of ORIGINAL leaves with a first singleton disagreement
witnessed by opposite 0-edges at its raw meet therefore has
exactly the SAME numerical first meet after every finite marker
stage: #1115 preserves all lower agreements, while the unchanged
0-witness prevents the meet from moving later.

The #1116 fixed-leaf-pair auxiliary equality at every cut yields
equality of the corresponding exact numerical auxiliary meets.
Finally, for any two ORIGINAL marked pairs, the full numerical
two-meet is unchanged as soon as their two coordinate singleton
meets are unchanged. This separates the remaining mixed-role
coordinate question from the already protected auxiliary part.

No enriched quotient, countable V3 completion, full mixed-meet
theorem, or target flip absorption is asserted.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The new cross-branch Devlin edges never have first endpoint 0. -/
theorem fillMissingDevlinLeafColumn_zero_first_iff
    (source G : Ordered3Graph Nat) (q y z : Nat) :
    (fillMissingDevlinLeafColumn source G q).edge 0 y z ↔
      G.edge 0 y z := by
  simp [fillMissingDevlinLeafColumn]

/-- Every original edge with first endpoint 0 is literally
unchanged after any finite number of marker-column updates. -/
theorem fillOriginalLeafColumns_zero_first_iff
    (R : Ordered3Graph Nat) (n y z : Nat) :
    (fillOriginalLeafColumns R n).edge 0 y z ↔
      R.edge 0 y z := by
  induction n with
  | zero =>
      simp [fillOriginalLeafColumns_zero]
  | succ n ih =>
      rw [fillOriginalLeafColumns_succ]
      by_cases hLeaf : DiaryLeafPriority.IsLeaf R n
      · have hStep :=
          fillMissingDevlinLeafColumn_zero_first_iff
            R (fillOriginalLeafColumns R n) n y z
        simpa [advanceOriginalLeafColumn, hLeaf] using hStep.trans ih
      · simpa [advanceOriginalLeafColumn, hLeaf] using ih

/-- The exact diary role of every original vertex is unchanged.
The predicate IsLeaf is defined solely by 0-1 and 0-2 role edges. -/
theorem fillOriginalLeafColumns_isLeaf_iff
    (R : Ordered3Graph Nat) (n v : Nat) :
    DiaryLeafPriority.IsLeaf (fillOriginalLeafColumns R n) v ↔
      DiaryLeafPriority.IsLeaf R v := by
  simp only [DiaryLeafPriority.IsLeaf,
    fillOriginalLeafColumns_zero_first_iff]

theorem fillOriginalLeafColumns_isOneSplit_iff
    (R : Ordered3Graph Nat) (n v : Nat) :
    DiaryLeafPriority.IsOneSplit (fillOriginalLeafColumns R n) v ↔
      DiaryLeafPriority.IsOneSplit R v := by
  simp only [DiaryLeafPriority.IsOneSplit,
    fillOriginalLeafColumns_zero_first_iff]

theorem fillOriginalLeafColumns_isTwoSplit_iff
    (R : Ordered3Graph Nat) (n v : Nat) :
    DiaryLeafPriority.IsTwoSplit (fillOriginalLeafColumns R n) v ↔
      DiaryLeafPriority.IsTwoSplit R v := by
  simp only [DiaryLeafPriority.IsTwoSplit,
    fillOriginalLeafColumns_zero_first_iff]

/-- The exact auxiliary meet of two already marked original pairs
is unchanged. This upgrades #1116's ALL-CUT auxiliary type iff
to the actual numerical maximal agreement cut. -/
theorem fillOriginalLeafColumns_auxMeetLevel_eq_of_fixed_pairs
    (R : Ordered3Graph Nat) (n a b c d : Nat)
    (hAB : R.edge 1 a b ∨ R.edge 2 a b)
    (hCD : R.edge 1 c d ∨ R.edge 2 c d) :
    (fillOriginalLeafColumns R n).auxMeetLevel a b c d =
      R.auxMeetLevel a b c d := by
  classical
  apply Nat.le_antisymm
  · have hTarget :=
      (fillOriginalLeafColumns R n).auxMeetLevel_agree a b c d
    have hRaw :=
      (fillOriginalLeafColumns_sameAux_iff_of_fixed_pairs
        R n ((fillOriginalLeafColumns R n).auxMeetLevel a b c d)
        a b c d hAB hCD).mp hTarget
    exact Nat.le_findGreatest
      ((fillOriginalLeafColumns R n).auxMeetLevel_le_min a b c d)
      hRaw
  · have hRaw := R.auxMeetLevel_agree a b c d
    have hTarget :=
      (fillOriginalLeafColumns_sameAux_iff_of_fixed_pairs
        R n (R.auxMeetLevel a b c d)
        a b c d hAB hCD).mpr hRaw
    exact Nat.le_findGreatest (R.auxMeetLevel_le_min a b c d) hTarget

/-- If the first raw singleton disagreement of two original leaves
is witnessed by an ORIGINAL split bit (0,m,a) versus (0,m,b),
then chronological marker completion preserves the exact numerical
one-meet. The raw first meet must lie at least at 3; there is no
hypothesis of an ambient full pre-diary or of type reflection. -/
theorem fillOriginalLeafColumns_oneMeetLevel_eq_of_zero_witness
    (R : Ordered3Graph Nat) (n a b : Nat)
    (ha : DiaryLeafPriority.IsLeaf R a)
    (hb : DiaryLeafPriority.IsLeaf R b)
    (hm3 : 3 ≤ R.oneMeetLevel a b)
    (hDifferent :
      ¬ (R.edge 0 (R.oneMeetLevel a b) a ↔
         R.edge 0 (R.oneMeetLevel a b) b)) :
    (fillOriginalLeafColumns R n).oneMeetLevel a b =
      R.oneMeetLevel a b := by
  classical
  have hCap : R.oneMeetLevel a b ≤ min a b :=
    R.oneMeetLevel_le_min a b
  have hAgree :
      (fillOriginalLeafColumns R n).SameOneTypeBelow
        (R.oneMeetLevel a b) a b :=
    fillOriginalLeafColumns_preserves_raw_one_prefix
      R n (R.oneMeetLevel a b) a b ha hb hCap
      (R.oneMeetLevel_agree a b)
  have hLower :
      R.oneMeetLevel a b ≤
        (fillOriginalLeafColumns R n).oneMeetLevel a b :=
    Nat.le_findGreatest hCap hAgree
  have hUpper :
      (fillOriginalLeafColumns R n).oneMeetLevel a b ≤
        R.oneMeetLevel a b := by
    by_contra hNot
    have hBeyond :
        R.oneMeetLevel a b <
          (fillOriginalLeafColumns R n).oneMeetLevel a b := by omega
    have hTargetSame :
        (fillOriginalLeafColumns R n).edge 0
          (R.oneMeetLevel a b) a ↔
          (fillOriginalLeafColumns R n).edge 0
            (R.oneMeetLevel a b) b :=
      (fillOriginalLeafColumns R n).oneMeetLevel_agree a b
        (by omega) hBeyond
    have hRawSame :
        R.edge 0 (R.oneMeetLevel a b) a ↔
          R.edge 0 (R.oneMeetLevel a b) b :=
      ((fillOriginalLeafColumns_zero_first_iff R n
        (R.oneMeetLevel a b) a).symm.trans hTargetSame).trans
        (fillOriginalLeafColumns_zero_first_iff R n
          (R.oneMeetLevel a b) b)
    exact hDifferent hRawSame
  exact Nat.le_antisymm hUpper hLower

/-- Reduction of numerical full 2-meet preservation to the two
coordinate 1-meets. The auxiliary meet is already fixed by #1116
and the preceding theorem. This is the exact remaining interface
for the mixed/capped source-role case analysis. -/
theorem fillOriginalLeafColumns_twoMeetLevel_eq_of_fixed_pairs_and_coords
    (R : Ordered3Graph Nat) (n a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hAB : R.edge 1 a b ∨ R.edge 2 a b)
    (hCD : R.edge 1 c d ∨ R.edge 2 c d)
    (hFirst :
      (fillOriginalLeafColumns R n).oneMeetLevel a c =
        R.oneMeetLevel a c)
    (hSecond :
      (fillOriginalLeafColumns R n).oneMeetLevel b d =
        R.oneMeetLevel b d) :
    (fillOriginalLeafColumns R n).twoMeetLevel a b c d =
      R.twoMeetLevel a b c d := by
  have hAux : (fillOriginalLeafColumns R n).auxMeetLevel a b c d =
      R.auxMeetLevel a b c d :=
    fillOriginalLeafColumns_auxMeetLevel_eq_of_fixed_pairs
      R n a b c d hAB hCD
  calc
    (fillOriginalLeafColumns R n).twoMeetLevel a b c d =
      min ((fillOriginalLeafColumns R n).auxMeetLevel a b c d)
        (min ((fillOriginalLeafColumns R n).oneMeetLevel a c)
             ((fillOriginalLeafColumns R n).oneMeetLevel b d)) :=
      (fillOriginalLeafColumns R n).twoMeetLevel_eq_min
        a b c d hab hcd
    _ = min (R.auxMeetLevel a b c d)
          (min (R.oneMeetLevel a c) (R.oneMeetLevel b d)) := by
      rw [hAux, hFirst, hSecond]
    _ = R.twoMeetLevel a b c d :=
      (R.twoMeetLevel_eq_min a b c d hab hcd).symm

end Ordered3Graph
end ThreeUniformDiaries
