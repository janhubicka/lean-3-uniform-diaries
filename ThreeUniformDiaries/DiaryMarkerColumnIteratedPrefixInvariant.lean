import ThreeUniformDiaries.DiaryMarkerColumnPrefixInvariant

/-!
# Track B: finite chronological leaf-pair marker-column induction

Merged PR #1112 proves the one-column common-prefix invariant.
We first extend it to an arbitrary later cut m, then define a GENUINE
LEAF-PAIR update: the earlier position q and the later endpoint z must
both be leaves in the frozen original raw graph. The earlier q guard
is enforced by advanceOriginalLeafColumn; the later z guard is inside
fillMissingDevlinLeafColumn.

This fixes an adversarially found edge-shape defect in an earlier draft:
filling a column at an original leaf q for all z>q (including splits)
would introduce forbidden Devlin marker edges. No such extra edges
are inserted here.

The final theorem is a one-way preservation of raw singleton-prefix
equalities on ORIGINAL LEAVES through ANY finite stage. It does not
assert global V3, a raw enriched flip quotient, protected mixed meets,
or target flip absorption.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Inserting missing markers at q preserves every old singleton
equality through an arbitrary cut m at or before both compared
vertices, whether q lies before the cut or after it. -/
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

/-- Corrected leaf-pair constructor: target endpoint z is
explicitly required to be a leaf of the original raw source.
The q-leaf guard is implemented separately in the iteration. -/
def fillMissingDevlinLeafColumn
    (source G : Ordered3Graph Nat) (q : Nat) :
    Ordered3Graph Nat where
  edge x y z :=
    G.edge x y z ∨
    (y = q ∧ q < z ∧ DiaryLeafPriority.IsLeaf source z ∧
      MissingDevlinPair G q z ∧
      ((x = 1 ∧ DiaryLeafPriority.LexEarlier G q z) ∨
       (x = 2 ∧ ¬ DiaryLeafPriority.LexEarlier G q z)))

/-- At a genuine original leaf endpoint z, the corrected
constructor agrees with the unrestricted generic column API. -/
theorem fillMissingDevlinLeafColumn_edge_iff_of_leaf
    (source G : Ordered3Graph Nat) (q x y z : Nat)
    (hz : DiaryLeafPriority.IsLeaf source z) :
    (fillMissingDevlinLeafColumn source G q).edge x y z ↔
      (fillMissingDevlinColumn G q).edge x y z := by
  simp [fillMissingDevlinLeafColumn, fillMissingDevlinColumn, hz]

/-- Exact arbitrary-cut singleton-prefix preservation for two
original LEAVES under the corrected role-safe leaf-pair update. -/
theorem fillMissingDevlinLeafColumn_preserves_one_prefix_at_cut
    (source G : Ordered3Graph Nat) (q m a b : Nat)
    (hq : 3 ≤ q)
    (ha : DiaryLeafPriority.IsLeaf source a)
    (hb : DiaryLeafPriority.IsLeaf source b)
    (hCap : m ≤ min a b)
    (hs : G.SameOneTypeBelow m a b) :
    (fillMissingDevlinLeafColumn source G q).SameOneTypeBelow m a b := by
  have hUnrestricted :=
    fillMissingDevlinColumn_preserves_one_prefix_at_cut
      G q m a b hq hCap hs
  intro i j hij hjm
  rw [fillMissingDevlinLeafColumn_edge_iff_of_leaf source G q i j a ha,
      fillMissingDevlinLeafColumn_edge_iff_of_leaf source G q i j b hb]
  exact hUnrestricted hij hjm

/-- Advance at q only if q is an original leaf; the fill
constructor additionally checks that its later endpoint is an
original leaf, preventing marker edges into split vertices. -/
noncomputable def advanceOriginalLeafColumn
    (source G : Ordered3Graph Nat) (q : Nat) :
    Ordered3Graph Nat := by
  classical
  exact if DiaryLeafPriority.IsLeaf source q then
    fillMissingDevlinLeafColumn source G q else G

/-- Process all original leaf columns q<n in increasing order.
Each new orientation reads LexEarlier in the evolving graph. -/
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

/-- Every raw singleton-type equality of ORIGINAL LEAVES at a
cut m≤min(a,b) survives an arbitrary finite number of the
role-safe chronological leaf-pair assignments. Only the
forward preservation is asserted. -/
theorem fillOriginalLeafColumns_preserves_raw_one_prefix
    (R : Ordered3Graph Nat) (n m a b : Nat)
    (ha : DiaryLeafPriority.IsLeaf R a)
    (hb : DiaryLeafPriority.IsLeaf R b)
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
          fillMissingDevlinLeafColumn_preserves_one_prefix_at_cut
            R (fillOriginalLeafColumns R n) n m a b
            hQ ha hb hCap ih
        simpa [advanceOriginalLeafColumn, hLeaf] using hStep
      · simpa [advanceOriginalLeafColumn, hLeaf] using ih

end Ordered3Graph
end ThreeUniformDiaries
