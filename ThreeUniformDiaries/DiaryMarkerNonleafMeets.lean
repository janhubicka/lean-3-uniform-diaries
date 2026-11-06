import ThreeUniformDiaries.DiaryMarkerNumericalMeets

/-!
# Track B: chronological marker columns do not move non-leaf and early meets

The new marker edges always end at an original leaf and have
their middle vertex at an original leaf, hence at level >= 3.
Consequently:
* every edge ending at a non-leaf is unchanged;
* every edge with middle vertex strictly below 3 is unchanged.

From the literal edge-derived cut definitions, the first assertion
preserves ALL non-leaf/non-leaf singleton meets, and the second
preserves EVERY singleton meet that was below marker cut 3.
These are the split/split and early-cut cases of protected branch
meets. The remaining split/leaf comparison can be reduced to the
second theorem by showing the original roles disagree below 3.

No global pre-diary, quotient, full protected embedding, or
flip-absorption theorem is assumed or claimed.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- No column update creates an edge ending at an original non-leaf. -/
theorem fillOriginalLeafColumns_edge_iff_nonleaf_terminal
    (R : Ordered3Graph Nat) (n x y z : Nat)
    (hz : ¬ DiaryLeafPriority.IsLeaf R z) :
    (fillOriginalLeafColumns R n).edge x y z ↔ R.edge x y z := by
  induction n with
  | zero =>
      simp [fillOriginalLeafColumns_zero]
  | succ n ih =>
      rw [fillOriginalLeafColumns_succ]
      by_cases hl : DiaryLeafPriority.IsLeaf R n
      · simpa [advanceOriginalLeafColumn, hl,
          fillMissingDevlinLeafColumn, hz] using ih
      · simpa [advanceOriginalLeafColumn, hl] using ih

/-- A new marker edge has middle coordinate an original leaf,
which is always at least 3. Thus all earlier-middle tests are
literally invariant, for arbitrary last vertices. -/
theorem fillOriginalLeafColumns_edge_iff_middle_lt_three
    (R : Ordered3Graph Nat) (n x y z : Nat)
    (hy : y < 3) :
    (fillOriginalLeafColumns R n).edge x y z ↔ R.edge x y z := by
  induction n with
  | zero =>
      simp [fillOriginalLeafColumns_zero]
  | succ n ih =>
      rw [fillOriginalLeafColumns_succ]
      by_cases hl : DiaryLeafPriority.IsLeaf R n
      · have hneq : y ≠ n := by
          have hn3 : 3 ≤ n := hl.1
          omega
        simpa [advanceOriginalLeafColumn, hl,
          fillMissingDevlinLeafColumn, hneq] using ih
      · simpa [advanceOriginalLeafColumn, hl] using ih

/-- Equality and inequality of singleton types of original non-leaf
endpoints are reflected through EVERY numerical cut. -/
theorem fillOriginalLeafColumns_sameOne_iff_nonleaf_pair
    (R : Ordered3Graph Nat) (n m a b : Nat)
    (ha : ¬ DiaryLeafPriority.IsLeaf R a)
    (hb : ¬ DiaryLeafPriority.IsLeaf R b) :
    (fillOriginalLeafColumns R n).SameOneTypeBelow m a b ↔
      R.SameOneTypeBelow m a b := by
  constructor
  · intro h x y hxy hym
    exact ((fillOriginalLeafColumns_edge_iff_nonleaf_terminal
      R n x y a ha).symm.trans (h hxy hym)).trans
        (fillOriginalLeafColumns_edge_iff_nonleaf_terminal
          R n x y b hb)
  · intro h x y hxy hym
    exact (fillOriginalLeafColumns_edge_iff_nonleaf_terminal
      R n x y a ha).trans ((h hxy hym).trans
        (fillOriginalLeafColumns_edge_iff_nonleaf_terminal
          R n x y b hb).symm)

/-- All singleton comparisons up to marker cut 3, on arbitrary
endpoints, remain literally unchanged. -/
theorem fillOriginalLeafColumns_sameOne_iff_cut_le_three
    (R : Ordered3Graph Nat) (n m a b : Nat)
    (hm : m ≤ 3) :
    (fillOriginalLeafColumns R n).SameOneTypeBelow m a b ↔
      R.SameOneTypeBelow m a b := by
  constructor
  · intro h x y hxy hym
    have hy3 : y < 3 := lt_of_lt_of_le hym hm
    exact ((fillOriginalLeafColumns_edge_iff_middle_lt_three
      R n x y a hy3).symm.trans (h hxy hym)).trans
        (fillOriginalLeafColumns_edge_iff_middle_lt_three
          R n x y b hy3)
  · intro h x y hxy hym
    have hy3 : y < 3 := lt_of_lt_of_le hym hm
    exact (fillOriginalLeafColumns_edge_iff_middle_lt_three
      R n x y a hy3).trans ((h hxy hym).trans
        (fillOriginalLeafColumns_edge_iff_middle_lt_three
          R n x y b hy3).symm)

/-- Exact numerical meet levels are determined by their complete
tables of agreement over all cuts not exceeding min(a,b). -/
theorem oneMeetLevel_eq_of_prefixIff_all_cuts
    (R G : Ordered3Graph Nat) (a b : Nat)
    (hIff : ∀ m, m ≤ min a b →
      (R.SameOneTypeBelow m a b ↔ G.SameOneTypeBelow m a b)) :
    G.oneMeetLevel a b = R.oneMeetLevel a b := by
  classical
  apply Nat.le_antisymm
  · have hCap := G.oneMeetLevel_le_min a b
    have hRaw :=
      (hIff (G.oneMeetLevel a b) hCap).mpr
        (G.oneMeetLevel_agree a b)
    exact Nat.le_findGreatest hCap hRaw
  · have hCap := R.oneMeetLevel_le_min a b
    have hTarget :=
      (hIff (R.oneMeetLevel a b) hCap).mp
        (R.oneMeetLevel_agree a b)
    exact Nat.le_findGreatest hCap hTarget

/-- All numerical singleton meets of two original non-leaves
are exactly invariant under chronological marker assignment. -/
theorem fillOriginalLeafColumns_oneMeetLevel_eq_nonleaf_pair
    (R : Ordered3Graph Nat) (n a b : Nat)
    (ha : ¬ DiaryLeafPriority.IsLeaf R a)
    (hb : ¬ DiaryLeafPriority.IsLeaf R b) :
    (fillOriginalLeafColumns R n).oneMeetLevel a b =
      R.oneMeetLevel a b := by
  apply oneMeetLevel_eq_of_prefixIff_all_cuts
  intro m hm
  exact (fillOriginalLeafColumns_sameOne_iff_nonleaf_pair
    R n m a b ha hb).symm

/-- If either original endpoint is one of the three distinguished
markers, its capped singleton meet lies at or before marker cut 3
and therefore cannot change in the finite chronological completion. -/
theorem fillOriginalLeafColumns_oneMeetLevel_eq_of_small_cap
    (R : Ordered3Graph Nat) (n a b : Nat)
    (hCap : min a b ≤ 3) :
    (fillOriginalLeafColumns R n).oneMeetLevel a b =
      R.oneMeetLevel a b := by
  apply oneMeetLevel_eq_of_prefixIff_all_cuts
  intro m hm
  exact (fillOriginalLeafColumns_sameOne_iff_cut_le_three
    R n m a b (le_trans hm hCap)).symm

end Ordered3Graph
end ThreeUniformDiaries
