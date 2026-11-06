import ThreeUniformDiaries.DiaryMarkerColumnIteratedPrefixInvariant
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Track B: raw positive pair types survive chronological Devlin markers

The verified column induction already preserves singleton-prefix equality
of original leaves. At a pair (a,b) whose raw Devlin marker is fixed,
no chronological step may add ANY new auxiliary edge (x,a,b):
the insertion guard tests that BOTH raw/current marker bits are absent.

Together, these facts show that a full positive pair-type equality at
a shared 2-split persists through any finite stage of leaf-pair marker
completion. The proof assumes only the explicit raw initial marker
existence on the two pairs and their source leaf roles, not a global
pre-diary, split witness, or flip absorption.

Important distinction: this proves preservation of equality, not an
exact meet-level identity or V3 on fixed branch leaf pairs.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- A marker-completion step only adds edges, never removes old ones. -/
theorem fillMissingDevlinLeafColumn_old_edge
    (source G : Ordered3Graph Nat) (q x y z : Nat)
    (h : G.edge x y z) :
    (fillMissingDevlinLeafColumn source G q).edge x y z := by
  exact Or.inl h

/-- Every original raw edge survives every finite chronological stage. -/
theorem fillOriginalLeafColumns_old_edge
    (R : Ordered3Graph Nat) (n x y z : Nat)
    (h : R.edge x y z) :
    (fillOriginalLeafColumns R n).edge x y z := by
  induction n with
  | zero =>
      simpa [fillOriginalLeafColumns_zero] using h
  | succ n ih =>
      rw [fillOriginalLeafColumns_succ]
      by_cases hl : DiaryLeafPriority.IsLeaf R n
      · simpa [advanceOriginalLeafColumn, hl] using
          (fillMissingDevlinLeafColumn_old_edge
            R (fillOriginalLeafColumns R n) n x y z ih)
      · simpa [advanceOriginalLeafColumn, hl] using ih

/-- If a pair already has a Devlin marker, the missing-marker
insertion does not alter ANY auxiliary test ending in that pair. -/
theorem fillMissingDevlinLeafColumn_edge_iff_of_fixed_pair
    (source G : Ordered3Graph Nat) (q x a b : Nat)
    (hFixed : G.edge 1 a b ∨ G.edge 2 a b) :
    (fillMissingDevlinLeafColumn source G q).edge x a b ↔
      G.edge x a b := by
  constructor
  · intro he
    change G.edge x a b ∨
      (a = q ∧ q < b ∧ DiaryLeafPriority.IsLeaf source b ∧
        MissingDevlinPair G q b ∧
        ((x = 1 ∧ DiaryLeafPriority.LexEarlier G q b) ∨
         (x = 2 ∧ ¬ DiaryLeafPriority.LexEarlier G q b))) at he
    rcases he with hOld | ⟨haq, _, _, hMissing, _⟩
    · exact hOld
    · have hAbsent : MissingDevlinPair G a b := by
        simpa only [haq] using hMissing
      exact (hFixed.elim (fun h => hAbsent.1 h)
        (fun h => hAbsent.2 h)).elim
  · exact fillMissingDevlinLeafColumn_old_edge source G q x a b

/-- On an originally marked pair, every auxiliary bit agrees with
the raw input after ANY finite number of marker assignments. The
first coordinate x is unrestricted (including all marker rows). -/
theorem fillOriginalLeafColumns_edge_iff_of_fixed_pair
    (R : Ordered3Graph Nat) (n x a b : Nat)
    (hFixed : R.edge 1 a b ∨ R.edge 2 a b) :
    (fillOriginalLeafColumns R n).edge x a b ↔
      R.edge x a b := by
  induction n with
  | zero =>
      simp [fillOriginalLeafColumns_zero]
  | succ n ih =>
      have hFixedNow :
          (fillOriginalLeafColumns R n).edge 1 a b ∨
            (fillOriginalLeafColumns R n).edge 2 a b := by
        rcases hFixed with h1 | h2
        · exact Or.inl (fillOriginalLeafColumns_old_edge R n 1 a b h1)
        · exact Or.inr (fillOriginalLeafColumns_old_edge R n 2 a b h2)
      rw [fillOriginalLeafColumns_succ]
      by_cases hl : DiaryLeafPriority.IsLeaf R n
      · have hStep :=
          fillMissingDevlinLeafColumn_edge_iff_of_fixed_pair
            R (fillOriginalLeafColumns R n) n x a b hFixedNow
        simpa [advanceOriginalLeafColumn, hl] using hStep.trans ih
      · simpa [advanceOriginalLeafColumn, hl] using ih

/-- Auxiliary-type equality on two originally marked ordered pairs
is preserved AND reflected at every numerical cut. No leaf roles or
diary axioms are needed, only an existing marker on each pair. -/
theorem fillOriginalLeafColumns_sameAux_iff_of_fixed_pairs
    (R : Ordered3Graph Nat) (n m a b c d : Nat)
    (hAB : R.edge 1 a b ∨ R.edge 2 a b)
    (hCD : R.edge 1 c d ∨ R.edge 2 c d) :
    (fillOriginalLeafColumns R n).SameAuxTypeBelow m a b c d ↔
      R.SameAuxTypeBelow m a b c d := by
  constructor
  · intro h i hi
    exact (fillOriginalLeafColumns_edge_iff_of_fixed_pair
      R n i a b hAB).symm.trans
        ((h i hi).trans
          (fillOriginalLeafColumns_edge_iff_of_fixed_pair
            R n i c d hCD))
  · intro h i hi
    exact (fillOriginalLeafColumns_edge_iff_of_fixed_pair
      R n i a b hAB).trans
        ((h i hi).trans
          (fillOriginalLeafColumns_edge_iff_of_fixed_pair
            R n i c d hCD).symm)

/-- Track B V2 preservation. Given two original marked LEAF pairs
a<b and c<d whose FULL pair types agree below a shared split cut m,
their full pair types still agree after any finite number of
chronological Devlin-marker assignments. Both coordinate one-types
are handled by the verified #1115 induction; the auxiliary
coordinate is literally unchanged by the fixed-pair theorem above.

This is the missing V2 positive-type transport, conditional only on
the raw positive-pair agreement and original marker existence.
The ambient enriched flip quotient still has to supply these inputs.
-/
theorem fillOriginalLeafColumns_preserves_positive_two_type
    (R : Ordered3Graph Nat) (n m a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : DiaryLeafPriority.IsLeaf R a)
    (hb : DiaryLeafPriority.IsLeaf R b)
    (hc : DiaryLeafPriority.IsLeaf R c)
    (hd : DiaryLeafPriority.IsLeaf R d)
    (hCut : m ≤ min a c)
    (hAB : R.edge 1 a b ∨ R.edge 2 a b)
    (hCD : R.edge 1 c d ∨ R.edge 2 c d)
    (hSame : R.SameTwoTypeBelow m a b c d) :
    (fillOriginalLeafColumns R n).SameTwoTypeBelow m a b c d := by
  have hCutSecond : m ≤ min b d := by
    have hma : m ≤ a := hCut.trans (min_le_left _ _)
    have hmc : m ≤ c := hCut.trans (min_le_right _ _)
    omega
  refine ⟨?_, ?_, ?_⟩
  · exact fillOriginalLeafColumns_preserves_raw_one_prefix
      R n m a c ha hc hCut hSame.1
  · exact fillOriginalLeafColumns_preserves_raw_one_prefix
      R n m b d hb hd hCutSecond hSame.2.1
  · exact (fillOriginalLeafColumns_sameAux_iff_of_fixed_pairs
      R n m a b c d hAB hCD).mpr hSame.2.2

end Ordered3Graph
end ThreeUniformDiaries
