import ThreeUniformDiaries.TypeTrees

/-!
# Extend a finite strictly increasing selected-level map to ω

Finite strong pictures of selected height k+1 only use the level
indices 0,...,k. Their chosen selected levels can be extended to
an infinite strictly increasing level map without changing any of
those initial values.

The canonical extension appends consecutive levels after the last
prescribed level. This trivial but essential interface is needed
when passing a finite picture to an infinite strong extension and
then using the verified infinite geometric-composition theorem.
-/

namespace ThreeUniformDiaries

/-- Extend the first k+1 values of a level map by consecutive
increments beyond its final prescribed value. -/
def extendFiniteLevelMap (lambda : Nat → Nat) (k : Nat) (i : Nat) : Nat :=
  if i ≤ k then lambda i else lambda k + (i - k)

/-- On the prescribed finite domain the extension is literal. -/
theorem extendFiniteLevelMap_eq_of_le
    (lambda : Nat → Nat) (k i : Nat) (hi : i ≤ k) :
    extendFiniteLevelMap lambda k i = lambda i := by
  simp [extendFiniteLevelMap, hi]

/-- The extension is strictly increasing, assuming only the
finite consecutive selected-level inequalities. -/
theorem extendFiniteLevelMap_strictMono
    (lambda : Nat → Nat) (k : Nat)
    (hsteps : ∀ i : Nat, i < k → lambda i < lambda (i + 1)) :
    StrictMono (extendFiniteLevelMap lambda k) := by
  apply strictMono_nat_of_lt_succ
  intro i
  by_cases hik : i < k
  · have hi : i ≤ k := by omega
    have his : i + 1 ≤ k := by omega
    simpa only [extendFiniteLevelMap, ite_eq_left hi, ite_eq_left his] using
      hsteps i hik
  · by_cases heq : i = k
    · subst i
      have hnot : ¬ k + 1 ≤ k := by omega
      simp only [extendFiniteLevelMap, ite_eq_left (le_refl k), ite_eq_right hnot]
      omega
    · have hki : k < i := by omega
      have hnoti : ¬ i ≤ k := by omega
      have hnots : ¬ i + 1 ≤ k := by omega
      simp only [extendFiniteLevelMap, ite_eq_right hnoti, ite_eq_right hnots]
      omega

/-- The extension equals its last finite selected level plus the
ordinary distance from the last index on every later index. -/
theorem extendFiniteLevelMap_eq_of_gt
    (lambda : Nat → Nat) (k i : Nat) (hi : k < i) :
    extendFiniteLevelMap lambda k i = lambda k + (i - k) := by
  simp [extendFiniteLevelMap, Nat.not_le.mpr hi]

end ThreeUniformDiaries
