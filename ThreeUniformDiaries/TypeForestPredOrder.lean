import ThreeUniformDiaries.CoordinateTree

/-!
# Canonical finite-height predecessor order of the ATR type forest

The root-glued ATR tree is genuinely rooted, and its coordinate
components each have a canonical predecessor: delete the last
ambient type coordinate, stopping at the level-zero component root.

We prove the exact Mathlib PredOrder axioms rather than assuming
an abstract rooted-tree model. Since levels lie in Nat, the strict
ancestor relation is well-founded, yielding finite predecessor
iterations from the general Archimedean theorem.
-/

namespace ThreeUniformDiaries
namespace CoordNode

def forestPred (a : CoordNode) : CoordNode :=
  if 0 < level a then truncate a (level a - 1) else a

theorem forestPred_le (a : CoordNode) : forestPred a ≤ a := by
  unfold forestPred
  split_ifs with h
  · exact truncate_le a (Nat.sub_le _ _)
  · exact le_refl a

theorem forestPred_level_of_pos
    (a : CoordNode) (h : 0 < level a) :
    level (forestPred a) = level a - 1 := by
  simp [forestPred, h]

theorem forestPred_isMin_of_le
    {a : CoordNode} (ha : a ≤ forestPred a) :
    IsMin a := by
  have hzero : level a = 0 := by
    by_contra hn
    have hpos : 0 < level a := by omega
    have hlev := level_le_of_le ha
    rw [forestPred_level_of_pos a hpos] at hlev
    omega
  intro b hba
  have hbl : level b = 0 := by
    have hle := level_le_of_le hba
    rw [hzero] at hle
    omega
  have heq : b = a :=
    eq_of_le_of_level_eq hba (hbl.trans hzero.symm)
  exact heq.symm.le

theorem forest_le_pred_of_lt
    {a b : CoordNode} (hab : a < b) :
    a ≤ forestPred b := by
  have hlt : level a < level b := level_lt_of_lt hab
  have hpos : 0 < level b := by omega
  have hle : level a ≤ level b - 1 := by omega
  unfold forestPred
  rw [if_pos hpos]
  refine ⟨by simpa using hle, ?_⟩
  change truncate (truncate b (level b - 1)) (level a) = a
  rw [truncate_truncate b hle]
  exact hab.le.2

noncomputable instance : PredOrder CoordNode where
  pred := forestPred
  pred_le := forestPred_le
  min_of_le_pred := by
    intro a ha
    exact forestPred_isMin_of_le ha
  le_pred_of_lt := by
    intro a b hab
    exact forest_le_pred_of_lt hab

theorem forest_strictRank {a b : CoordNode} (hab : a < b) :
    level a < level b := level_lt_of_lt hab

instance : WellFoundedLT CoordNode :=
  (measure level).wf.mono (by
    intro a b hab
    exact forest_strictRank hab)

theorem forest_exists_pred_iterate_of_le
    {a b : CoordNode} (hab : a ≤ b) :
    ∃ k : Nat, (Order.pred^[k]) b = a :=
  exists_pred_iterate_of_le hab

end CoordNode
end ThreeUniformDiaries
