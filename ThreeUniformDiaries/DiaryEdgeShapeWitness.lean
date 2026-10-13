import ThreeUniformDiaries.DiaryAuxTransferWitness

/-!
# Marker witnesses from the concrete diary edge-shape axioms

For a diary leaf pair a<b whose singleton meet is the 1-split m,
the manuscript's restrictions on the five permitted edge forms
force the witness at m to occur with first vertex 0.

This module derives the three auxiliary bounds required for the
ATR-admissibility of the pointed 3-vertex envelope, without
assuming the branch disagreement separately.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The two E/V clauses of the role-based diary definition used
in the pointed-envelope proof: a 1-split is seen from an earlier
coordinate only through the zero marker, and each ordered pair
of leaves has a marker at 1 or 2. -/
structure SplitEdgeShape (H : Ordered3Graph Nat) : Prop where
  oneSplit_earlier_only_zero :
    ∀ m a z, IsOneSplit H m → IsLeaf H a →
      z < m → z ≠ 0 → ¬ H.edge z m a
  leaf_pair_marker :
    ∀ a b, a < b → IsLeaf H a → IsLeaf H b →
      H.edge 1 a b ∨ H.edge 2 a b

/-- If two singleton type codes first differ at a non-capped
meet m, some earlier z<m gives an edge disagreement at m. -/
theorem oneMeetLevel_has_first_witness
    (H : Ordered3Graph Nat) (a b m : Nat)
    (hm : H.oneMeetLevel a b = m)
    (hma : m < a) (hmb : m < b) :
    ∃ z, z < m ∧ ¬ (H.edge z m a ↔ H.edge z m b) := by
  have hagree : H.SameOneTypeBelow m a b := by
    rw [← hm]
    exact H.oneMeetLevel_agree a b
  have hfail : ¬ H.SameOneTypeBelow (m + 1) a b := by
    intro h
    have hbound : m + 1 ≤ min a b := by omega
    have hbad : m + 1 ≤ H.oneMeetLevel a b := by
      exact Nat.le_findGreatest
        (P := fun k => H.SameOneTypeBelow k a b) hbound h
    omega
  classical
  have hwitness : ∃ z, z < m ∧
      ¬ (H.edge z m a ↔ H.edge z m b) := by
    by_contra hn
    have hall : ∀ z, z < m →
        (H.edge z m a ↔ H.edge z m b) := by
      intro z hz
      by_contra hdiff
      exact hn ⟨z, hz, hdiff⟩
    exact hfail ((H.sameOneTypeBelow_succ_iff m a b).mpr
      ⟨hagree, hall⟩)
  exact hwitness

/-- A 1-split witness between two leaves must be detected by
opposite zero-marker edges. -/
theorem oneSplit_branch_zero
    (H : Ordered3Graph Nat) (shape : SplitEdgeShape H)
    (m a b : Nat) (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hm : IsOneSplit H m)
    (hmeet : H.oneMeetLevel a b = m)
    (hma : m < a) (hmb : m < b) :
    (H.edge 0 m a ∧ ¬ H.edge 0 m b) ∨
      (¬ H.edge 0 m a ∧ H.edge 0 m b) := by
  obtain ⟨z, hzm, hdiff⟩ :=
    oneMeetLevel_has_first_witness H a b m hmeet hma hmb
  have hz0 : z = 0 := by
    by_contra hz
    have hnoa := shape.oneSplit_earlier_only_zero m a z hm ha hzm hz
    have hnob := shape.oneSplit_earlier_only_zero m b z hm hb hzm hz
    exact hdiff (iff_of_false hnoa hnob)
  subst z
  by_cases hea : H.edge 0 m a
  · left
    refine ⟨hea, ?_⟩
    intro heb
    exact hdiff (iff_of_true hea heb)
  · right
    refine ⟨hea, ?_⟩
    by_contra hnb
    exact hdiff (iff_of_false hea hnb)

/-- The three auxiliary meets of the corresponding pointed envelope
are bounded by the fixed markers 0,1,2, using only (E/V) edge
restrictions and the actual full singleton meet at m. -/
theorem oneSplit_pointed_aux_bounds
    (H : Ordered3Graph Nat) (shape : SplitEdgeShape H)
    (m a b : Nat) (hab : a < b)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hm : IsOneSplit H m)
    (hmeet : H.oneMeetLevel a b = m)
    (hma : m < a) (hmb : m < b) :
    H.auxMeetLevel m a m b = 0 ∧
      H.auxMeetLevel m a a b ≤ 2 ∧
      H.auxMeetLevel m b a b ≤ 2 := by
  have hbranch := oneSplit_branch_zero H shape m a b ha hb
    hm hmeet hma hmb
  have hmarker := shape.leaf_pair_marker a b hab ha hb
  have hm1 : 1 < m := by
    have hbound := hm.1
    omega
  have hm2 : 2 < m := by
    have hbound := hm.1
    omega
  have hno1a := shape.oneSplit_earlier_only_zero m a 1
    hm ha hm1 (by omega)
  have hno2a := shape.oneSplit_earlier_only_zero m a 2
    hm ha hm2 (by omega)
  have hno1b := shape.oneSplit_earlier_only_zero m b 1
    hm hb hm1 (by omega)
  have hno2b := shape.oneSplit_earlier_only_zero m b 2
    hm hb hm2 (by omega)
  exact split_leaf_triple_aux_bounds H m a b
    hbranch hmarker hno1a hno2a hno1b hno2b

end DiaryLeafPriority
end ThreeUniformDiaries
