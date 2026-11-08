import ThreeUniformDiaries.DiaryFiniteOrderTowerColimitObstruction

/-!
# Track B: exact Nat-carrier criterion for towers of finite linear orders

The finite strong-absorber tower has selected bounded, order-increasing
transition embeddings, but these maps need not be literal initial-segment
inclusions. This abstract theorem isolates the separate carrier question.

An increasing finite-frame tower has a coherent order realization in Nat
if and only if the future numerical rank of each fixed old vertex is
bounded uniformly over ALL later finite horizons. This is a FINITE ORDER
theorem, not a full RoleDiary colimit or countable-source absorption.

Importantly, each transition and each proposed limit map need only
be strictly increasing ON ITS FINITE FRAME. No hidden global StrictMono
assumption on Nat is used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Finite enumerated linear-order frames and bounded successor maps.
No diary roles, edges, or meet operations are required. -/
structure FiniteOrderTransitionTower where
  size : Nat → Nat
  step : Nat → Nat → Nat
  step_strict : ∀ n u v : Nat, u < v → v < size n →
    step n u < step n v
  step_bound : ∀ n u : Nat, u < size n →
    step n u < size (n+1)

namespace FiniteOrderTransitionTower

/-- The chosen composite from stage n to stage n+k. -/
def forward (T : FiniteOrderTransitionTower) (n k : Nat) : Nat → Nat :=
  Nat.rec (fun u : Nat => u)
    (fun j f u => T.step (n+j) (f u)) k

@[simp] theorem forward_zero (T : FiniteOrderTransitionTower) (n u : Nat) :
    T.forward n 0 u = u := rfl

@[simp] theorem forward_succ (T : FiniteOrderTransitionTower) (n k u : Nat) :
    T.forward n (k+1) u =
      T.step (n+k) (T.forward n k u) := rfl

/-- Every composite stays inside the actual finite target frame. -/
theorem forward_bound (T : FiniteOrderTransitionTower)
    (n k u : Nat) (hu : u < T.size n) :
    T.forward n k u < T.size (n+k) := by
  induction k with
  | zero =>
      simpa only [Nat.add_zero, forward_zero] using hu
  | succ k ih =>
      simpa only [Nat.add_succ, forward_succ] using
        T.step_bound (n+k) (T.forward n k u) ih

/-- Each composite remains strictly increasing on its finite source frame. -/
theorem forward_strict (T : FiniteOrderTransitionTower)
    (n k u v : Nat) (huv : u < v) (hv : v < T.size n) :
    T.forward n k u < T.forward n k v := by
  induction k with
  | zero =>
      simpa only [forward_zero] using huv
  | succ k ih =>
      simpa only [forward_succ] using
        T.step_strict (n+k) _ _ ih (T.forward_bound n k v hv)

/-- A finite-frame strictly increasing Nat map cannot move an element
to a smaller numerical rank. -/
private theorem finite_strict_ge_index
    (N : Nat) (f : Nat → Nat)
    (h : ∀ u v : Nat, u < v → v < N → f u < f v) :
    ∀ u : Nat, u < N → u ≤ f u := by
  intro u
  induction u with
  | zero =>
      intro _
      omega
  | succ t ih =>
      intro hu
      have hprev : t ≤ f t := ih (by omega)
      have hnext : f t < f (t+1) := h t (t+1) (by omega) hu
      omega

theorem step_ge_index (T : FiniteOrderTransitionTower)
    (n u : Nat) (hu : u < T.size n) :
    u ≤ T.step n u :=
  finite_strict_ge_index (T.size n) (T.step n)
    (T.step_strict n) u hu

theorem forward_le_succ (T : FiniteOrderTransitionTower)
    (n k u : Nat) (hu : u < T.size n) :
    T.forward n k u ≤ T.forward n (k+1) u := by
  simpa only [forward_succ] using
    T.step_ge_index (n+k) (T.forward n k u)
      (T.forward_bound n k u hu)

/-- Numerical rank of a fixed old vertex never decreases along the tower. -/
theorem forward_mono_horizon (T : FiniteOrderTransitionTower)
    (n u : Nat) (hu : u < T.size n) :
    Monotone (fun k : Nat => T.forward n k u) := by
  apply monotone_nat_of_le_succ
  intro k
  exact T.forward_le_succ n k u hu

/-- A composite beginning with the first successor map is the same
literal function value as the shifted composite. -/
theorem forward_shift (T : FiniteOrderTransitionTower)
    (n k u : Nat) :
    T.forward n (k+1) u =
      T.forward (n+1) k (T.step n u) := by
  induction k with
  | zero =>
      simp only [forward_zero, forward_succ, Nat.add_zero]
  | succ k ih =>
      calc
        T.forward n ((k+1)+1) u =
          T.step (n+(k+1)) (T.forward n (k+1) u) := rfl
        _ = T.step ((n+1)+k)
              (T.forward (n+1) k (T.step n u)) := by
          have hn : n+(k+1) = (n+1)+k := by omega
          rw [hn, ih]
        _ = T.forward (n+1) (k+1) (T.step n u) := rfl

/-- Bound each fixed original vertex independently of the later horizon. -/
def BoundedRanks (T : FiniteOrderTransitionTower) : Prop :=
  ∀ n u : Nat, u < T.size n →
    ∃ M : Nat, ∀ k : Nat, T.forward n k u < M

/-- Compatibility and strict monotonicity are requested ONLY on the
actual finite frames. Total Nat functions are notation conveniences. -/
def NatOrderRealization (T : FiniteOrderTransitionTower) : Prop :=
  ∃ g : Nat → Nat → Nat,
    (∀ n u v : Nat, u < v → v < T.size n → g n u < g n v) ∧
    (∀ n u : Nat, u < T.size n →
      g (n+1) (T.step n u) = g n u)

/-- Coherence for one step gives coherence across any finite horizon. -/
theorem realization_forward_coherent (T : FiniteOrderTransitionTower)
    (g : Nat → Nat → Nat)
    (hCompat : ∀ n u : Nat, u < T.size n →
      g (n+1) (T.step n u) = g n u)
    (n u : Nat) (hu : u < T.size n) (k : Nat) :
    g (n+k) (T.forward n k u) = g n u := by
  induction k with
  | zero =>
      simp only [Nat.add_zero, forward_zero]
  | succ k ih =>
      have hstep :=
        hCompat (n+k) (T.forward n k u) (T.forward_bound n k u hu)
      calc
        g (n+(k+1)) (T.forward n (k+1) u) =
          g ((n+k)+1) (T.step (n+k) (T.forward n k u)) := by
            simp only [Nat.add_succ, forward_succ]
        _ = g (n+k) (T.forward n k u) := hstep
        _ = g n u := ih

/-- A coherent Nat realization provides a numeric bound on every
old vertex's rank across ALL future stages. -/
theorem boundedRanks_of_realization (T : FiniteOrderTransitionTower)
    (h : T.NatOrderRealization) : T.BoundedRanks := by
  obtain ⟨g, hMono, hCompat⟩ := h
  intro n u hu
  refine ⟨g n u + 1, ?_⟩
  intro k
  have hframe := T.forward_bound n k u hu
  have hge : T.forward n k u ≤
      g (n+k) (T.forward n k u) :=
    finite_strict_ge_index (T.size (n+k))
      (g (n+k)) (hMono (n+k)) _ hframe
  have hcoh := T.realization_forward_coherent
    g hCompat n u hu k
  omega

/-- Elementary bounded-monotone-Nat stabilization, with no compactness
assumption or appeal to an order-completion theorem. -/
private theorem eventually_constant_of_bounded_monotone_nat
    (r : Nat → Nat) (hr : Monotone r) :
    ∀ M : Nat, (∀ k : Nat, r k ≤ M) →
      ∃ K : Nat, ∀ k : Nat, K ≤ k → r k = r K := by
  intro M
  induction M with
  | zero =>
      intro hb
      refine ⟨0, ?_⟩
      intro k _
      have h0 := hb 0
      have hk := hb k
      omega
  | succ M ih =>
      intro hb
      by_cases hsmall : ∀ k : Nat, r k ≤ M
      · exact ih hsmall
      · push_neg at hsmall
        obtain ⟨K, hK⟩ := hsmall
        refine ⟨K, ?_⟩
        intro k hk
        have hle : r K ≤ r k := hr hk
        have htop := hb k
        have hKtop := hb K
        omega

/-- Every fixed old rank eventually stops moving if it has a single
numerical upper bound uniform in the future horizon. -/
theorem exists_stable_forward_rank (T : FiniteOrderTransitionTower)
    (hb : T.BoundedRanks)
    (n u : Nat) (hu : u < T.size n) :
    ∃ v : Nat, ∃ K : Nat, ∀ k : Nat, K ≤ k →
      T.forward n k u = v := by
  obtain ⟨M, hM⟩ := hb n u hu
  have hle : ∀ k : Nat, T.forward n k u ≤ M := by
    intro k
    have := hM k
    omega
  obtain ⟨K, hK⟩ :=
    eventually_constant_of_bounded_monotone_nat
      (fun k : Nat => T.forward n k u)
      (T.forward_mono_horizon n u hu) M hle
  exact ⟨T.forward n K u, K, hK⟩

/-- Canonical eventually constant ranks give a coherent realization
in Nat. In particular, no arbitrary choice of source copies is made. -/
theorem realization_of_boundedRanks (T : FiniteOrderTransitionTower)
    (hb : T.BoundedRanks) : T.NatOrderRealization := by
  classical
  let g : Nat → Nat → Nat := fun n u =>
    if hu : u < T.size n then
      Classical.choose (T.exists_stable_forward_rank hb n u hu)
    else 0
  have hstable : ∀ n u : Nat, u < T.size n →
      ∃ K : Nat, ∀ k : Nat, K ≤ k →
        T.forward n k u = g n u := by
    intro n u hu
    have hspec :=
      Classical.choose_spec (T.exists_stable_forward_rank hb n u hu)
    simpa only [g, dif_pos hu] using hspec
  refine ⟨g, ?_, ?_⟩
  · intro n u v huv hv
    have hu : u < T.size n := by omega
    obtain ⟨Ku, hKu⟩ := hstable n u hu
    obtain ⟨Kv, hKv⟩ := hstable n v hv
    let k := max Ku Kv
    have hlu := hKu k (by
      dsimp [k]
      exact le_max_left _ _)
    have hlv := hKv k (by
      dsimp [k]
      exact le_max_right _ _)
    have hlt := T.forward_strict n k u v huv hv
    omega
  · intro n u hu
    have hstep := T.step_bound n u hu
    obtain ⟨Ku, hKu⟩ := hstable n u hu
    obtain ⟨Kv, hKv⟩ := hstable (n+1) (T.step n u) hstep
    let k := max Ku Kv
    have hlu := hKu (k+1) (by
      dsimp [k]
      exact le_trans (le_max_left _ _) (Nat.le_succ _))
    have hlv := hKv k (by
      dsimp [k]
      exact le_max_right _ _)
    rw [T.forward_shift n k u, hlv] at hlu
    exact hlu

/-- Exact finite-order carrier criterion, with the weak and correct
finite-frame monotonicity hypothesis on all transition/limit maps.
This is NOT a countable diary colimit or a flip-absorption theorem. -/
theorem natOrderRealization_iff_boundedRanks
    (T : FiniteOrderTransitionTower) :
    T.NatOrderRealization ↔ T.BoundedRanks := by
  constructor
  · exact T.boundedRanks_of_realization
  · exact T.realization_of_boundedRanks

end FiniteOrderTransitionTower
end DiaryLeafPriority
end ThreeUniformDiaries
