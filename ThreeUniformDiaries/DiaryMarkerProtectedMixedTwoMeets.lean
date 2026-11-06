import ThreeUniformDiaries.DiaryMarkerMixedSingletonMeets
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Track B: exact mixed and capped two-meets in protected branch pictures

A new chronological Devlin marker edge ALWAYS has two original leaves
as its final pair. Consequently an auxiliary pair (a,b) is frozen
if either endpoint is a nonleaf. A pair of original leaves is frozen
if its two-marker Devlin choice was already assigned in the raw graph,
by verified Track B PR #1116.

Call a pair PROTECTED when either condition holds. On protected pairs
ALL auxiliary tests are literally unchanged; the numerical auxiliary
meet and both directions of auxiliary type agreement follow. Using the
fully case-split singleton meet theorem (stacked dependency), the
standard min-decomposition gives exact full 2-meet preservation for
ANY two protected ordered pairs, including arbitrary split/leaf mixes
and capped comparisons.

The source assumptions remain explicit: the raw branch must have
original markers on each within-branch leaf pair, and distinct leaf
coordinate comparisons must have an original 0-split-edge first
disagreement witness. This is a conditional branch-local theorem,
NOT construction of the enriched quotient, a V/E pre-diary or
every-target-flip absorption.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- An old pair is protected from new marker edges if it is
already Devlin-marked, or at least one endpoint is NOT a leaf.
For arbitrary increasing branch pairs of a genuine diary this is
automatic; it is not asserted for arbitrary cross-branch leaf pairs. -/
def OriginalProtectedAuxPair
    (R : Ordered3Graph Nat) (a b : Nat) : Prop :=
  (R.edge 1 a b ∨ R.edge 2 a b) ∨
    ¬ DiaryLeafPriority.IsLeaf R a ∨
    ¬ DiaryLeafPriority.IsLeaf R b

/-- New Devlin edges cannot terminate at (a,b) if at least one
endpoint was an original non-leaf. This includes pairs containing
markers or splits in either coordinate. -/
theorem fillOriginalLeafColumns_edge_iff_pair_with_nonleaf
    (R : Ordered3Graph Nat) (n x a b : Nat)
    (hNonleaf : ¬ DiaryLeafPriority.IsLeaf R a ∨
       ¬ DiaryLeafPriority.IsLeaf R b) :
    (fillOriginalLeafColumns R n).edge x a b ↔
      R.edge x a b := by
  induction n with
  | zero =>
      simp [fillOriginalLeafColumns_zero]
  | succ n ih =>
      rw [fillOriginalLeafColumns_succ]
      by_cases hLeaf : DiaryLeafPriority.IsLeaf R n
      · rcases hNonleaf with hA | hB
        · have hne : a ≠ n := by
            intro he
            apply hA
            simpa only [he] using hLeaf
          simpa [advanceOriginalLeafColumn, hLeaf,
            fillMissingDevlinLeafColumn, hne] using ih
        · simpa [advanceOriginalLeafColumn, hLeaf,
            fillMissingDevlinLeafColumn, hB] using ih
      · simpa [advanceOriginalLeafColumn, hLeaf] using ih

/-- All auxiliary tests of a protected original pair are unchanged
after ANY finite number of marker assignments. -/
theorem fillOriginalLeafColumns_edge_iff_protected_aux_pair
    (R : Ordered3Graph Nat) (n x a b : Nat)
    (h : OriginalProtectedAuxPair R a b) :
    (fillOriginalLeafColumns R n).edge x a b ↔
      R.edge x a b := by
  rcases h with hFixed | (hA | hB)
  · exact fillOriginalLeafColumns_edge_iff_of_fixed_pair
      R n x a b hFixed
  · exact fillOriginalLeafColumns_edge_iff_pair_with_nonleaf
      R n x a b (Or.inl hA)
  · exact fillOriginalLeafColumns_edge_iff_pair_with_nonleaf
      R n x a b (Or.inr hB)

/-- Both preservation and REFLECTION of full auxiliary type
agreement at every numerical cut for two protected old pairs. -/
theorem fillOriginalLeafColumns_sameAux_iff_protected_pairs
    (R : Ordered3Graph Nat) (n m a b c d : Nat)
    (hAB : OriginalProtectedAuxPair R a b)
    (hCD : OriginalProtectedAuxPair R c d) :
    (fillOriginalLeafColumns R n).SameAuxTypeBelow m a b c d ↔
      R.SameAuxTypeBelow m a b c d := by
  constructor
  · intro h i hi
    exact ((fillOriginalLeafColumns_edge_iff_protected_aux_pair
      R n i a b hAB).symm.trans
        (h (a := i) hi)).trans
        (fillOriginalLeafColumns_edge_iff_protected_aux_pair
          R n i c d hCD)
  · intro h i hi
    exact (fillOriginalLeafColumns_edge_iff_protected_aux_pair
      R n i a b hAB).trans
        ((h (a := i) hi).trans
          (fillOriginalLeafColumns_edge_iff_protected_aux_pair
            R n i c d hCD).symm)

/-- Equality of the EXACT numerical auxiliary meet for arbitrary
protected original pairs, including mixed split/leaf and capped cases. -/
theorem fillOriginalLeafColumns_auxMeetLevel_eq_protected_pairs
    (R : Ordered3Graph Nat) (n a b c d : Nat)
    (hAB : OriginalProtectedAuxPair R a b)
    (hCD : OriginalProtectedAuxPair R c d) :
    (fillOriginalLeafColumns R n).auxMeetLevel a b c d =
      R.auxMeetLevel a b c d := by
  classical
  apply Nat.le_antisymm
  · have hCap :=
      (fillOriginalLeafColumns R n).auxMeetLevel_le_min a b c d
    have hRaw :
        R.SameAuxTypeBelow
          ((fillOriginalLeafColumns R n).auxMeetLevel a b c d)
          a b c d :=
      (fillOriginalLeafColumns_sameAux_iff_protected_pairs
        R n ((fillOriginalLeafColumns R n).auxMeetLevel a b c d)
        a b c d hAB hCD).mp
        ((fillOriginalLeafColumns R n).auxMeetLevel_agree a b c d)
    exact Nat.le_findGreatest hCap hRaw
  · have hCap := R.auxMeetLevel_le_min a b c d
    have hTarget :
        (fillOriginalLeafColumns R n).SameAuxTypeBelow
          (R.auxMeetLevel a b c d) a b c d :=
      (fillOriginalLeafColumns_sameAux_iff_protected_pairs
        R n (R.auxMeetLevel a b c d)
        a b c d hAB hCD).mpr
        (R.auxMeetLevel_agree a b c d)
    exact Nat.le_findGreatest hCap hTarget

/-- Exact full two-meet of ANY TWO protected ordered pairs is
reduced to exact coordinate singleton meets. The auxiliary-meet
part is fully discharged and does not require the pairs to be
both-leaf pairs. -/
theorem fillOriginalLeafColumns_twoMeetLevel_eq_protected_pairs_of_coords
    (R : Ordered3Graph Nat) (n a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hAB : OriginalProtectedAuxPair R a b)
    (hCD : OriginalProtectedAuxPair R c d)
    (hFirst :
      (fillOriginalLeafColumns R n).oneMeetLevel a c =
        R.oneMeetLevel a c)
    (hSecond :
      (fillOriginalLeafColumns R n).oneMeetLevel b d =
        R.oneMeetLevel b d) :
    (fillOriginalLeafColumns R n).twoMeetLevel a b c d =
      R.twoMeetLevel a b c d := by
  have hAux :
      (fillOriginalLeafColumns R n).auxMeetLevel a b c d =
        R.auxMeetLevel a b c d :=
    fillOriginalLeafColumns_auxMeetLevel_eq_protected_pairs
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

/-- Exact full numerical two-meets within a protected raw branch
picture. Every nonleaf-containing auxiliary pair is automatically
protected; leaf/leaf auxiliary pairs need original Devlin marker
bits. The two coordinate leaf/leaf comparisons need genuine
0-edge first-disagreement witnesses, as supplied by a diary branch.
All mixed split/leaf, diagonal and capped cases are included. -/
theorem fillOriginalLeafColumns_twoMeetLevel_eq_of_protected_picture
    (R : Ordered3Graph Nat) (n a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hAB : OriginalProtectedAuxPair R a b)
    (hCD : OriginalProtectedAuxPair R c d)
    (hFirstWitness :
      DiaryLeafPriority.IsLeaf R a →
      DiaryLeafPriority.IsLeaf R c →
      a ≠ c →
      3 ≤ R.oneMeetLevel a c ∧
        ¬ (R.edge 0 (R.oneMeetLevel a c) a ↔
           R.edge 0 (R.oneMeetLevel a c) c))
    (hSecondWitness :
      DiaryLeafPriority.IsLeaf R b →
      DiaryLeafPriority.IsLeaf R d →
      b ≠ d →
      3 ≤ R.oneMeetLevel b d ∧
        ¬ (R.edge 0 (R.oneMeetLevel b d) b ↔
           R.edge 0 (R.oneMeetLevel b d) d)) :
    (fillOriginalLeafColumns R n).twoMeetLevel a b c d =
      R.twoMeetLevel a b c d := by
  exact fillOriginalLeafColumns_twoMeetLevel_eq_protected_pairs_of_coords
    R n a b c d hab hcd hAB hCD
    (fillOriginalLeafColumns_oneMeetLevel_eq_of_protected_pair
      R n a c hFirstWitness)
    (fillOriginalLeafColumns_oneMeetLevel_eq_of_protected_pair
      R n b d hSecondWitness)

end Ordered3Graph
end ThreeUniformDiaries
