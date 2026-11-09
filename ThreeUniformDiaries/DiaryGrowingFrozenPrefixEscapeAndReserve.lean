import ThreeUniformDiaries.DiaryFiniteOrderTowerNatCarrierCriterion

/-!
# Track B: expanding frozen fronts do NOT imply bounded old ranks

Finite linear order frames [0,2n+4), with each transition fixing
[0,n+3) and sending u >= n+3 to u+2, have an escaping original
vertex at rank three: forward(0,k,3)=3+2k.

This is a pure finite-order counterexample. It is NOT a counterexample
to the actual full finite diary absorber tower.

We also give a sufficient reserved-image criterion: if transition n
places EVERY old vertex below the NEXT protected cut and the
nondecreasing cuts are fixed literally by all successor maps, then
each old vertex stabilizes after its first transition. No such
reserved-image theorem for finite full diaries is assumed or proved.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At stage n, fix the expanding prefix [0,n+3), while inserting
two fresh positions just before every old remaining vertex. -/
def frozenPrefixEscapeStep (n u : Nat) : Nat :=
  if u < n+3 then u else u+2

/-- An actual bounded, strictly increasing finite order tower with
unbounded frame sizes, three fixed markers, and growing literal
frozen prefixes. -/
def frozenPrefixEscapeTower : FiniteOrderTransitionTower where
  size := fun n => 2*n+4
  step := frozenPrefixEscapeStep
  step_strict := by
    intro n u v huv hv
    dsimp [frozenPrefixEscapeStep]
    split_ifs <;> omega
  step_bound := by
    intro n u hu
    dsimp [frozenPrefixEscapeStep]
    split_ifs <;> omega

/-- Every successor freezes a prefix whose length tends to infinity. -/
theorem frozenPrefixEscapeTower_step_fixed
    (n u : Nat) (hu : u < n+3) :
    frozenPrefixEscapeTower.step n u = u := by
  simp [frozenPrefixEscapeTower, frozenPrefixEscapeStep, hu]

theorem frozenPrefixEscapeTower_unbounded :
    ∀ r : Nat, ∃ n : Nat, r < frozenPrefixEscapeTower.size n := by
  intro r
  refine ⟨r, ?_⟩
  dsimp [frozenPrefixEscapeTower]
  omega

/-- The original rank 3 lies outside the current frozen front at
EVERY stage: it moves by two at each selected transition. -/
theorem frozenPrefixEscapeTower_forward_three
    (k : Nat) :
    frozenPrefixEscapeTower.forward 0 k 3 = 3+2*k := by
  induction k with
  | zero =>
      simp only [FiniteOrderTransitionTower.forward_zero]
  | succ k ih =>
      calc
        frozenPrefixEscapeTower.forward 0 (k+1) 3 =
            frozenPrefixEscapeStep k
              (frozenPrefixEscapeTower.forward 0 k 3) := by
                simp only [FiniteOrderTransitionTower.forward_succ,
                  Nat.zero_add]
                rfl
        _ = frozenPrefixEscapeStep k (3+2*k) := by rw [ih]
        _ = 3+2*(k+1) := by
              unfold frozenPrefixEscapeStep
              have hOutside : ¬ 3+2*k < k+3 := by omega
              simp only [if_neg hOutside]
              omega

/-- Thus growing frozen prefixes alone are strictly weaker than
the uniform rank bounds required for a Nat-order realization. -/
theorem frozenPrefixEscapeTower_not_boundedRanks :
    ¬ frozenPrefixEscapeTower.BoundedRanks := by
  intro hBound
  obtain ⟨M,hM⟩ := hBound 0 3 (by norm_num [frozenPrefixEscapeTower])
  have h := hM M
  rw [frozenPrefixEscapeTower_forward_three M] at h
  omega

theorem frozenPrefixEscapeTower_no_NatOrderRealization :
    ¬ frozenPrefixEscapeTower.NatOrderRealization := by
  intro hReal
  exact frozenPrefixEscapeTower_not_boundedRanks
    (frozenPrefixEscapeTower.boundedRanks_of_realization hReal)

namespace FiniteOrderTransitionTower

/-- A strong RESERVE invariant: every old image lies below the next
reserved cut, and each selected transition fixes its own cut.
The cuts must be nondecreasing. No full-diary extension property
with this reserve has been established. -/
theorem forward_stabilizes_after_one_of_reserved_cuts
    (T : FiniteOrderTransitionTower) (r : Nat → Nat)
    (hCutMono : Monotone r)
    (hImageReserve : ∀ n u : Nat, u < T.size n →
      T.step n u < r (n+1))
    (hFix : ∀ n v : Nat, v < r n → T.step n v = v)
    (n u : Nat) (hu : u < T.size n) (k : Nat) :
    T.forward n (k+1) u = T.step n u := by
  induction k with
  | zero =>
      simp only [forward_succ, forward_zero, Nat.add_zero]
  | succ k ih =>
      have hFutureCut : r (n+1) ≤ r (n+(k+1)) :=
        hCutMono (by omega)
      have hImage : T.step n u < r (n+(k+1)) :=
        lt_of_lt_of_le (hImageReserve n u hu) hFutureCut
      calc
        T.forward n ((k+1)+1) u =
          T.step (n+(k+1)) (T.forward n (k+1) u) := rfl
        _ = T.step (n+(k+1)) (T.step n u) := by rw [ih]
        _ = T.step n u := hFix (n+(k+1)) (T.step n u) hImage

/-- Every selected old frame vertex is bounded after one step if
the selected image is captured by a protected, nondecreasing front. -/
theorem boundedRanks_of_reserved_cuts
    (T : FiniteOrderTransitionTower) (r : Nat → Nat)
    (hCutMono : Monotone r)
    (hImageReserve : ∀ n u : Nat, u < T.size n →
      T.step n u < r (n+1))
    (hFix : ∀ n v : Nat, v < r n → T.step n v = v) :
    T.BoundedRanks := by
  intro n u hu
  refine ⟨T.step n u + 1, ?_⟩
  intro k
  cases k with
  | zero =>
      have hSource : u ≤ T.step n u := T.step_ge_index n u hu
      simpa only [forward_zero] using
        (show u < T.step n u + 1 by omega)
  | succ k =>
      rw [T.forward_stabilizes_after_one_of_reserved_cuts
        r hCutMono hImageReserve hFix n u hu k]
      omega

/-- A reserved-image tower has an actual coherent Nat order carrier.
This theorem is purely CONDITIONAL on reserved cuts, and does
not claim their existence for the finite strong-absorber tower. -/
theorem natOrderRealization_of_reserved_cuts
    (T : FiniteOrderTransitionTower) (r : Nat → Nat)
    (hCutMono : Monotone r)
    (hImageReserve : ∀ n u : Nat, u < T.size n →
      T.step n u < r (n+1))
    (hFix : ∀ n v : Nat, v < r n → T.step n v = v) :
    T.NatOrderRealization :=
  T.realization_of_boundedRanks
    (T.boundedRanks_of_reserved_cuts r hCutMono hImageReserve hFix)

end FiniteOrderTransitionTower
end DiaryLeafPriority
end ThreeUniformDiaries
