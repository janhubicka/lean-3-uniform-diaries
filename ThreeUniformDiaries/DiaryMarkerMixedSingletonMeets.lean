import ThreeUniformDiaries.DiaryMarkerNonleafMeets

/-!
# Track B: complete case split for protected singleton meet levels

The merged zero-edge witness theorem handles two DISTINCT original
leaves when their first disagreement is at an actual one-split.
The previous non-leaf and small-cut lemmas handle split/split and
marker comparisons. This file completes the split/leaf comparison:

An original leaf has both role edges (0,1,-),(0,2,-) absent.
An original non-leaf at level >=3 has at least one present.
Thus their first singleton type disagreement is below cut 3.
The chronological marker construction does not change any of those
early-middle tests, so the exact meet stays unchanged.

The last theorem packages ALL original vertex pair cases under the
single explicit hypothesis that each DISTINCT pair of leaves in
the selected protected picture has a genuine 0-edge witness at
its raw first meet. That is a BRANCH-local condition, not an
assumption about arbitrary cross-branch pairs.

No enriched prefix quotient, V/E pre-diary, global completion,
or every-target-flip absorption is asserted.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Numerical self-meets are exactly the vertex itself for
every ordered graph, without diary or edge-order assumptions. -/
theorem oneMeetLevel_self_any (R : Ordered3Graph Nat) (a : Nat) :
    R.oneMeetLevel a a = a := by
  classical
  apply Nat.le_antisymm
  · simpa using R.oneMeetLevel_le_min a a
  · have hRefl : R.SameOneTypeBelow a a a := by
      intro x y hxy hy
      rfl
    exact Nat.le_findGreatest (by simp) hRefl

/-- A failure of singleton agreement through marker cut 3 forces
the numerical first meet strictly below 3. -/
theorem oneMeetLevel_lt_three_of_not_same_at_three
    (R : Ordered3Graph Nat) (a b : Nat)
    (hBad : ¬ R.SameOneTypeBelow 3 a b) :
    R.oneMeetLevel a b < 3 := by
  by_contra hNot
  have h3 : 3 ≤ R.oneMeetLevel a b := by omega
  have hSame : R.SameOneTypeBelow 3 a b := by
    intro x y hxy hy
    exact (R.oneMeetLevel_agree a b) hxy (lt_of_lt_of_le hy h3)
  exact hBad hSame

/-- If an ORIGINAL singleton meet occurs before cut 3, it is
preserved numerically, because ALL tests below that cut are fixed.
This includes markers and capped comparisons without requiring
an edge-derived role axiom. -/
theorem fillOriginalLeafColumns_oneMeetLevel_eq_of_raw_meet_lt_three
    (R : Ordered3Graph Nat) (n a b : Nat)
    (hRawLt : R.oneMeetLevel a b < 3) :
    (fillOriginalLeafColumns R n).oneMeetLevel a b =
      R.oneMeetLevel a b := by
  classical
  have hTargetLt :
      (fillOriginalLeafColumns R n).oneMeetLevel a b < 3 := by
    by_contra hNot
    have h3 :
        3 ≤ (fillOriginalLeafColumns R n).oneMeetLevel a b := by
      omega
    have hCap : 3 ≤ min a b :=
      le_trans h3
        ((fillOriginalLeafColumns R n).oneMeetLevel_le_min a b)
    have hTargetSame :
        (fillOriginalLeafColumns R n).SameOneTypeBelow 3 a b := by
      intro x y hxy hy
      exact (fillOriginalLeafColumns R n).oneMeetLevel_agree a b
        hxy (lt_of_lt_of_le hy h3)
    have hRawSame : R.SameOneTypeBelow 3 a b :=
      (fillOriginalLeafColumns_sameOne_iff_cut_le_three
        R n 3 a b (by omega)).mp hTargetSame
    have hRaw3 : 3 ≤ R.oneMeetLevel a b :=
      Nat.le_findGreatest hCap hRawSame
    omega
  apply Nat.le_antisymm
  · have hCap :=
      (fillOriginalLeafColumns R n).oneMeetLevel_le_min a b
    have hRawSame : R.SameOneTypeBelow
        ((fillOriginalLeafColumns R n).oneMeetLevel a b) a b :=
      (fillOriginalLeafColumns_sameOne_iff_cut_le_three
        R n ((fillOriginalLeafColumns R n).oneMeetLevel a b)
        a b (by omega)).mp
        ((fillOriginalLeafColumns R n).oneMeetLevel_agree a b)
    exact Nat.le_findGreatest hCap hRawSame
  · have hCap := R.oneMeetLevel_le_min a b
    have hTargetSame :
        (fillOriginalLeafColumns R n).SameOneTypeBelow
          (R.oneMeetLevel a b) a b :=
      (fillOriginalLeafColumns_sameOne_iff_cut_le_three
        R n (R.oneMeetLevel a b) a b (by omega)).mpr
        (R.oneMeetLevel_agree a b)
    exact Nat.le_findGreatest hCap hTargetSame

/-- A non-leaf at an original level >=3 has at least one
role marker; this is simply the negation of IsLeaf. -/
theorem nonleaf_has_role_marker
    (R : Ordered3Graph Nat) (v : Nat)
    (hv3 : 3 ≤ v) (hNotLeaf : ¬ DiaryLeafPriority.IsLeaf R v) :
    R.edge 0 1 v ∨ R.edge 0 2 v := by
  by_contra hNot
  have h01 : ¬ R.edge 0 1 v := by
    intro h
    exact hNot (Or.inl h)
  have h02 : ¬ R.edge 0 2 v := by
    intro h
    exact hNot (Or.inr h)
  exact hNotLeaf ⟨hv3, h01, h02⟩

/-- Two original vertices of different leaf/non-leaf status at
levels >=3 have different singleton types already below cut 3. -/
theorem not_same_one_at_three_of_mixed_leaf_status
    (R : Ordered3Graph Nat) (a b : Nat)
    (ha3 : 3 ≤ a) (hb3 : 3 ≤ b)
    (hMixed :
      (DiaryLeafPriority.IsLeaf R a ∧
       ¬ DiaryLeafPriority.IsLeaf R b) ∨
      (¬ DiaryLeafPriority.IsLeaf R a ∧
       DiaryLeafPriority.IsLeaf R b)) :
    ¬ R.SameOneTypeBelow 3 a b := by
  intro hSame
  rcases hMixed with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases nonleaf_has_role_marker R b hb3 hb with h1 | h2
    · exact ha.2.1
        ((hSame (a := 0) (b := 1) (by omega) (by omega)).mpr h1)
    · exact ha.2.2
        ((hSame (a := 0) (b := 2) (by omega) (by omega)).mpr h2)
  · rcases nonleaf_has_role_marker R a ha3 ha with h1 | h2
    · exact hb.2.1
        ((hSame (a := 0) (b := 1) (by omega) (by omega)).mp h1)
    · exact hb.2.2
        ((hSame (a := 0) (b := 2) (by omega) (by omega)).mp h2)

/-- Split/leaf numerical meets are fixed: if one endpoint lies
among markers, the low-cap result applies; otherwise both are >=3
and the role markers give a pre-3 type disagreement. -/
theorem fillOriginalLeafColumns_oneMeetLevel_eq_of_mixed_leaf_status
    (R : Ordered3Graph Nat) (n a b : Nat)
    (hMixed :
      (DiaryLeafPriority.IsLeaf R a ∧
       ¬ DiaryLeafPriority.IsLeaf R b) ∨
      (¬ DiaryLeafPriority.IsLeaf R a ∧
       DiaryLeafPriority.IsLeaf R b)) :
    (fillOriginalLeafColumns R n).oneMeetLevel a b =
      R.oneMeetLevel a b := by
  by_cases hSmall : min a b ≤ 3
  · exact fillOriginalLeafColumns_oneMeetLevel_eq_of_small_cap
      R n a b hSmall
  · have ha3 : 3 ≤ a := by omega
    have hb3 : 3 ≤ b := by omega
    have hRawLt : R.oneMeetLevel a b < 3 :=
      oneMeetLevel_lt_three_of_not_same_at_three
        R a b
        (not_same_one_at_three_of_mixed_leaf_status
          R a b ha3 hb3 hMixed)
    exact fillOriginalLeafColumns_oneMeetLevel_eq_of_raw_meet_lt_three
      R n a b hRawLt

/-- A SINGLE branch-local hypothesis about distinct original
leaves completes ALL vertex-pair singleton numerical meet cases.
For non-leaf pairs and split/leaf pairs no extra hypothesis
is used. For two distinct leaves, the first raw singleton
disagreement must be an actual 0-split-edge witness.
This is exactly what a genuine diary branch supplies. -/
theorem fillOriginalLeafColumns_oneMeetLevel_eq_of_protected_pair
    (R : Ordered3Graph Nat) (n a b : Nat)
    (hWitness :
      DiaryLeafPriority.IsLeaf R a →
      DiaryLeafPriority.IsLeaf R b →
      a ≠ b →
      3 ≤ R.oneMeetLevel a b ∧
        ¬ (R.edge 0 (R.oneMeetLevel a b) a ↔
           R.edge 0 (R.oneMeetLevel a b) b)) :
    (fillOriginalLeafColumns R n).oneMeetLevel a b =
      R.oneMeetLevel a b := by
  by_cases ha : DiaryLeafPriority.IsLeaf R a
  · by_cases hb : DiaryLeafPriority.IsLeaf R b
    · by_cases hab : a = b
      · subst b
        calc
          (fillOriginalLeafColumns R n).oneMeetLevel a a = a :=
            oneMeetLevel_self_any (fillOriginalLeafColumns R n) a
          _ = R.oneMeetLevel a a :=
            (oneMeetLevel_self_any R a).symm
      · obtain ⟨hm3, hDiff⟩ := hWitness ha hb hab
        exact fillOriginalLeafColumns_oneMeetLevel_eq_of_zero_witness
          R n a b ha hb hm3 hDiff
    · exact fillOriginalLeafColumns_oneMeetLevel_eq_of_mixed_leaf_status
        R n a b (Or.inl ⟨ha, hb⟩)
  · by_cases hb : DiaryLeafPriority.IsLeaf R b
    · exact fillOriginalLeafColumns_oneMeetLevel_eq_of_mixed_leaf_status
        R n a b (Or.inr ⟨ha, hb⟩)
    · exact fillOriginalLeafColumns_oneMeetLevel_eq_nonleaf_pair
        R n a b ha hb

end Ordered3Graph
end ThreeUniformDiaries
