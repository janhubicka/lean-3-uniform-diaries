import ThreeUniformDiaries.DiaryMarkerColumnPrefixInvariant

/-!
# Track B: finite chronological marker-column induction

The merged one-column lemma says that adding the missing two Devlin
marker bits at an earlier position q cannot destroy an existing
singleton-prefix equality through q+1. Extend this to ANY later cut m:
updates at q < m use the one-column theorem, and those at q >= m
are invisible to the m-prefix.

Then iterate exactly the columns whose ORIGINAL vertices are leaves.
No marker is inserted at a split, and no later update can split a
raw singleton-prefix equality. This is a structural invariant only:
the global V3, all protected mixed meets, enriched quotient and flip
absorption are separate mathematical obligations.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Inserting the missing Devlin markers at q preserves every
old one-type equality through an arbitrary cut m at or before
both target vertices, not only through q+1. -/
theorem fillMissingDevlinColumn_preserves_one_prefix_at_cut
    (R : Ordered3Graph Nat) (q m a b : Nat)
    (hq : 3 ≤ q) (hCap : m ≤ min a b)
    (hs : R.SameOneTypeBelow m a b) :
    (fillMissingDevlinColumn R q).SameOneTypeBelow m a b := by
  have hMa : m ≤ a := le_trans hCap (min_le_left a b)
  have hMb : m ≤ b := le_trans hCap (min_le_right a b)
  by_cases hqm : q < m
  · have hqa : q < a := by omega
    have hqb : q < b := by omega
    have hNext : R.SameOneTypeBelow (q+1) a b := by
      intro i j hij hjq
      exact hs hij (by omega)
    have hColumn :=
      fillMissingDevlinColumn_preserves_one_prefix
        R q a b hq hqa hqb hNext
    intro i j hij hjm
    by_cases hjq : j = q
    · subst j
      exact hColumn hij (by omega)
    · have hRaw : R.edge i j a ↔ R.edge i j b :=
        hs hij hjm
      change
        (R.edge i j a ∨
          (j = q ∧ q < a ∧ MissingDevlinPair R q a ∧
            ((i = 1 ∧ DiaryLeafPriority.LexEarlier R q a) ∨
             (i = 2 ∧ ¬ DiaryLeafPriority.LexEarlier R q a)))) ↔
        (R.edge i j b ∨
          (j = q ∧ q < b ∧ MissingDevlinPair R q b ∧
            ((i = 1 ∧ DiaryLeafPriority.LexEarlier R q b) ∨
             (i = 2 ∧ ¬ DiaryLeafPriority.LexEarlier R q b))))
      simpa [hjq] using hRaw
  · intro i j hij hjm
    have hjq : j ≠ q := by omega
    have hRaw : R.edge i j a ↔ R.edge i j b :=
      hs hij hjm
    change
      (R.edge i j a ∨
        (j = q ∧ q < a ∧ MissingDevlinPair R q a ∧
          ((i = 1 ∧ DiaryLeafPriority.LexEarlier R q a) ∨
           (i = 2 ∧ ¬ DiaryLeafPriority.LexEarlier R q a)))) ↔
      (R.edge i j b ∨
        (j = q ∧ q < b ∧ MissingDevlinPair R q b ∧
          ((i = 1 ∧ DiaryLeafPriority.LexEarlier R q b) ∨
           (i = 2 ∧ ¬ DiaryLeafPriority.LexEarlier R q b))))
    simpa [hjq] using hRaw

/-- Add the marker column at q precisely if q is a genuine
leaf in the ORIGINAL raw graph; otherwise leave the current
graph unchanged. Role edges are never modified by this step. -/
noncomputable def advanceOriginalLeafColumn
    (R G : Ordered3Graph Nat) (q : Nat) : Ordered3Graph Nat := by
  classical
  exact if DiaryLeafPriority.IsLeaf R q then
    fillMissingDevlinColumn G q else G

/-- Stage n of the chronological assignment: process original
positions q < n in increasing order, touching only original leaves.
This recurrence uses the evolving graph for LexEarlier choices. -/
noncomputable def fillOriginalLeafColumns
    (R : Ordered3Graph Nat) (n : Nat) : Ordered3Graph Nat := by
  classical
  exact Nat.rec R (fun q G => advanceOriginalLeafColumn R G q) n

theorem fillOriginalLeafColumns_zero (R : Ordered3Graph Nat) :
    fillOriginalLeafColumns R 0 = R := by
  simp [fillOriginalLeafColumns]

theorem fillOriginalLeafColumns_succ
    (R : Ordered3Graph Nat) (n : Nat) :
    fillOriginalLeafColumns R (n+1) =
      advanceOriginalLeafColumn R (fillOriginalLeafColumns R n) n := by
  simp [fillOriginalLeafColumns]

/-- Every raw singleton equality below m survives ANY finite
number of chronological leaf-column assignments, including
columns before m. This is the finite global form of the
common-prefix preservation invariant; it does not assert
that raw-distinct types remain distinct. -/
theorem fillOriginalLeafColumns_preserves_raw_one_prefix
    (R : Ordered3Graph Nat) (n m a b : Nat)
    (hCap : m ≤ min a b)
    (hs : R.SameOneTypeBelow m a b) :
    (fillOriginalLeafColumns R n).SameOneTypeBelow m a b := by
  induction n with
  | zero =>
      simpa [fillOriginalLeafColumns_zero] using hs
  | succ n ih =>
      rw [fillOriginalLeafColumns_succ]
      by_cases hLeaf : DiaryLeafPriority.IsLeaf R n
      · have hQ : 3 ≤ n := hLeaf.1
        have hStep :=
          fillMissingDevlinColumn_preserves_one_prefix_at_cut
            (fillOriginalLeafColumns R n) n m a b hQ hCap ih
        simpa [advanceOriginalLeafColumn, hLeaf] using hStep
      · simpa [advanceOriginalLeafColumn, hLeaf] using ih

end Ordered3Graph
end ThreeUniformDiaries
