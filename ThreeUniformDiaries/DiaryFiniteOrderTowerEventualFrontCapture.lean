import ThreeUniformDiaries.DiaryFiniteOrderTowerNatCarrierCriterion

/-!
# Track B: exact finite-injury characterization by EVENTUAL CAPTURE

An expanding numerical prefix fixed by the chosen successor maps
does not by itself prevent an old vertex from escaping faster
than that prefix. The correct additional condition is POINTWISE:
every old vertex must eventually enter some fixed reserved front.

For nondecreasing reserved cuts r_n that are literally fixed by
each transition, and assuming r_n are unbounded, eventual capture
is EQUIVALENT to pointwise uniform bounds on future old ranks.
This is a pure finite-order theorem, NOT a finite diary extension
theorem, an actual chosen absorber-tower rank estimate, or a
countable-source flip-absorption result.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteOrderTransitionTower

/-- Every old vertex enters a selected protected front at some
possibly vertex-dependent finite stage. -/
def EventualFrontCapture (T : FiniteOrderTransitionTower)
    (r : Nat → Nat) : Prop :=
  ∀ n u : Nat, u < T.size n →
    ∃ k : Nat, T.forward n k u < r (n+k)

/-- After a selected old vertex enters a literally fixed front,
its numerical rank is CONSTANT at every later horizon.
No bound on the number of revisions before capture is assumed. -/
theorem forward_stable_after_front_capture
    (T : FiniteOrderTransitionTower) (r : Nat → Nat)
    (hCutMono : Monotone r)
    (hFixed : ∀ n v : Nat, v < r n → T.step n v = v)
    (n u k : Nat) (hu : u < T.size n)
    (hCaptured : T.forward n k u < r (n+k))
    (j : Nat) :
    T.forward n (k+j) u = T.forward n k u := by
  induction j with
  | zero =>
      simp only [Nat.add_zero]
  | succ j ih =>
      have hCut : r (n+k) ≤ r (n+(k+j)) :=
        hCutMono (by omega)
      have hStill : T.forward n k u < r (n+(k+j)) :=
        lt_of_lt_of_le hCaptured hCut
      calc
        T.forward n (k+(j+1)) u =
            T.step (n+(k+j)) (T.forward n (k+j) u) := by
          have hIdx : k+(j+1) = (k+j)+1 := by omega
          rw [hIdx]
          exact T.forward_succ n (k+j) u
        _ = T.step (n+(k+j)) (T.forward n k u) := by
          rw [ih]
        _ = T.forward n k u := hFixed (n+(k+j)) _ hStill

/-- Pointwise eventual capture gives an explicit single uniform
future image bound, even when the capture time is different for
each old vertex. Earlier images are <= the captured image since
numerical ranks never decrease under finite order embeddings. -/
theorem boundedRanks_of_eventualFrontCapture
    (T : FiniteOrderTransitionTower) (r : Nat → Nat)
    (hCutMono : Monotone r)
    (hFixed : ∀ n v : Nat, v < r n → T.step n v = v)
    (hCapture : T.EventualFrontCapture r) :
    T.BoundedRanks := by
  intro n u hu
  obtain ⟨k,hCap⟩ := hCapture n u hu
  refine ⟨T.forward n k u + 1, ?_⟩
  intro j
  by_cases hj : j ≤ k
  · have hLe : T.forward n j u ≤ T.forward n k u :=
      T.forward_mono_horizon n u hu hj
    omega
  · have hkj : k ≤ j := by omega
    have hStable := T.forward_stable_after_front_capture
      r hCutMono hFixed n u k hu hCap (j-k)
    have hEq : k+(j-k) = j := by omega
    rw [hEq] at hStable
    rw [hStable]
    omega

/-- Conversely, every pointwise bounded old rank eventually becomes
constant. If protected fronts are NONDECREASING and UNBOUNDED,
the fixed eventual numerical rank must eventually lie inside one. -/
theorem eventualFrontCapture_of_boundedRanks
    (T : FiniteOrderTransitionTower) (r : Nat → Nat)
    (hCutMono : Monotone r)
    (hFrontUnbounded : ∀ M : Nat, ∃ j : Nat, M < r j)
    (hb : T.BoundedRanks) :
    T.EventualFrontCapture r := by
  intro n u hu
  obtain ⟨v,K,hStable⟩ := T.exists_stable_forward_rank hb n u hu
  obtain ⟨j,hj⟩ := hFrontUnbounded v
  let k : Nat := max K j
  refine ⟨k, ?_⟩
  have hK : K ≤ k := by dsimp [k]; exact le_max_left _ _
  have hStage : j ≤ n+k := by dsimp [k]; omega
  have hVal : T.forward n k u = v := hStable k hK
  rw [hVal]
  exact lt_of_lt_of_le hj (hCutMono hStage)

/-- Sharp finite-injury carrier criterion, with all quantifiers:
nondecreasing unbounded protected prefixes remain literally
fixed, and each old vertex eventually enters one iff every
old vertex has a horizon-independent bound on its selected rank. -/
theorem boundedRanks_iff_eventualFrontCapture
    (T : FiniteOrderTransitionTower) (r : Nat → Nat)
    (hCutMono : Monotone r)
    (hFrontUnbounded : ∀ M : Nat, ∃ j : Nat, M < r j)
    (hFixed : ∀ n v : Nat, v < r n → T.step n v = v) :
    T.BoundedRanks ↔ T.EventualFrontCapture r := by
  constructor
  · exact T.eventualFrontCapture_of_boundedRanks
      r hCutMono hFrontUnbounded
  · exact T.boundedRanks_of_eventualFrontCapture
      r hCutMono hFixed

end FiniteOrderTransitionTower
end DiaryLeafPriority
end ThreeUniformDiaries
