import ThreeUniformDiaries.DiaryFiniteOrderTowerNatCarrierCriterion

/-!
# Track B: eventual LITERAL initial-segment stability from bounded tower ranks

For an increasing finite-linear-order tower with unbounded finite
frame sizes, pointwise bounded selected forward ranks imply MORE than
existence of a Nat carrier: for every finite numerical cut r, from
some finite stage onward ALL selected successor maps fix every u<r.

The proof uses ONLY finite-frame monotonicity, exact selected
composition, and eventual constancy of nondecreasing Nat ranks.
The statement is a finite ORDER result, not a RoleDiary colimit
or countable-source flip-absorption theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteOrderTransitionTower

/-- A strictly increasing finite-frame successor that fixes rank v
must fix every smaller rank. Crucially we do not assume global
monotonicity of the underlying total Nat function. -/
theorem step_fixed_below
    (T : FiniteOrderTransitionTower)
    (n v : Nat)
    (hv : v < T.size n)
    (hFixed : T.step n v = v)
    (u : Nat) (hu : u ≤ v) :
    T.step n u = u := by
  have huFrame : u < T.size n := by omega
  have hLower := T.step_ge_index n u huFrame
  have hGap : ∀ t : Nat, u ≤ t → t < T.size n →
      T.step n u + (t-u) ≤ T.step n t := by
    intro t hle
    induction t, hle using Nat.le_induction with
    | base =>
        intro _
        omega
    | succ t hut ih =>
        intro ht
        have hprev : t < T.size n := by omega
        have hstep : T.step n t < T.step n (t+1) :=
          T.step_strict n t (t+1) (by omega) ht
        have hgap := ih hprev
        omega
  have hBound := hGap v hu hv
  omega

/-- If the frames are unbounded and every selected old vertex
has a horizon-independent future numerical rank bound, then every
finite initial segment eventually becomes literally stationary
under ALL following selected successor maps. -/
theorem exists_eventually_fixed_initial_segments
    (T : FiniteOrderTransitionTower)
    (hb : T.BoundedRanks)
    (hUnbounded : ∀ r : Nat, ∃ n : Nat, r < T.size n)
    (r : Nat) :
    ∃ N : Nat, ∀ k u : Nat, u < r → T.step (N+k) u = u := by
  obtain ⟨n,hr⟩ := hUnbounded r
  obtain ⟨v,K,hStable⟩ :=
    T.exists_stable_forward_rank hb n r hr
  have hvr : r ≤ v := by
    have hmon := T.forward_mono_horizon n r hr
    calc
      r = T.forward n 0 r := rfl
      _ ≤ T.forward n K r := hmon (Nat.zero_le K)
      _ = v := hStable K le_rfl
  refine ⟨n+K, ?_⟩
  intro k u hu
  let j : Nat := K+k
  have hj : K ≤ j := by dsimp [j]; omega
  have hj1 : K ≤ j+1 := by dsimp [j]; omega
  have hjval : T.forward n j r = v := hStable j hj
  have hjnext : T.forward n (j+1) r = v :=
    hStable (j+1) hj1
  have hvFrame : v < T.size (n+j) := by
    have hf := T.forward_bound n j r hr
    rw [hjval] at hf
    exact hf
  have hStepFixed : T.step (n+j) v = v := by
    have hrec := T.forward_succ n j r
    rw [hjval] at hrec
    rw [hjnext] at hrec
    exact hrec.symm
  have hAtStage : T.step (n+j) u = u :=
    T.step_fixed_below (n+j) v hvFrame hStepFixed u
      (by omega)
  have hIndex : (n+K)+k = n+j := by
    dsimp [j]
    omega
  simpa only [hIndex] using hAtStage

/-- After the finite cut stabilizes, every individual later
successor map fixes all ranks below that cut. In particular,
the actual finite diagram on that cut cannot move along the
selected transition embeddings. The diary structure still
requires a separate limit construction. -/
theorem eventually_fixed_prefix_from_nat_realization
    (T : FiniteOrderTransitionTower)
    (hRealization : T.NatOrderRealization)
    (hUnbounded : ∀ r : Nat, ∃ n : Nat, r < T.size n)
    (r : Nat) :
    ∃ N : Nat, ∀ k u : Nat, u < r → T.step (N+k) u = u := by
  exact T.exists_eventually_fixed_initial_segments
    (T.boundedRanks_of_realization hRealization)
    hUnbounded r

end FiniteOrderTransitionTower
end DiaryLeafPriority
end ThreeUniformDiaries
