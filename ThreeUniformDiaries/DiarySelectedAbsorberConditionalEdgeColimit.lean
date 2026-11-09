import ThreeUniformDiaries.DiaryFiniteEdgeTowerColimit
import ThreeUniformDiaries.DiarySelectedTowerNatCarrierBridge
import ThreeUniformDiaries.DiarySelectedStrongAbsorberTowerUnboundedFrames
import ThreeUniformDiaries.DiaryFiniteOrderTowerEventuallyFixedPrefix

/-!
# Track B: actual selected strong-absorber tower has a conditional
# countable induced EDGE TABLE limit

The selected finite strong-absorber targets and their bounded all-meet
embeddings are already kernel-verified. Their frame sizes are unbounded.
Conditionally on the still-UNPROVED pointwise bound on future numerical
ranks of all old target vertices, the transition maps eventually fix
every literal finite prefix, and the genuine finite edge/nonedge tables
stabilize there.

We use precisely the actual selected target maps, NOT unrelated
hypothetical copies. The resulting countable Ordered3Graph is not yet
asserted to be a full RoleDiary: global split witnesses, V3 marker
orientation and all numerical meet transfer remain separate checks.
The source-copy fusion/strong every-target-flip theorem is also OPEN.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

namespace FiniteOrderTransitionTower

/-- Bounded strictly increasing finite-frame maps cannot decrease
finite frame sizes. This is derived from the selected actual
step's bounded-image condition, including the empty-frame case. -/
theorem size_le_succ (T : FiniteOrderTransitionTower) (n : Nat) :
    T.size n ≤ T.size (n+1) := by
  by_cases hZero : T.size n = 0
  · omega
  · have hu : T.size n - 1 < T.size n := by omega
    have hBound := T.step_bound n (T.size n - 1) hu
    have hLower := T.step_ge_index n (T.size n - 1) hu
    omega

theorem size_mono (T : FiniteOrderTransitionTower) :
    ∀ a b : Nat, a ≤ b → T.size a ≤ T.size b := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ b hab ih =>
      exact le_trans ih (T.size_le_succ b)

end FiniteOrderTransitionTower

/-- The EDGE table tower consists of exactly the genuine selected
finite full-diary targets. All induced edge/nonedge transport is
supplied by the verified selected bounded all-meet embeddings. -/
noncomputable def selectedAbsorberFiniteEdgeTower :
    FiniteInducedEdgeTower where
  size := fun n => (universalStrongAbsorberTower n).bound
  step := universalStrongAbsorberTower_stepMap
  edge := fun n a b c => (universalStrongAbsorberTower n).graph.edge a b c
  edge_ordered := by
    intro n a b c he
    have hSupport :=
      (universalStrongAbsorberTower n).diary.prediary.frame.edge_support
        a b c he
    exact ⟨hSupport.1,hSupport.2.1⟩
  step_induced := by
    intro n a b c hab hbc hc
    have h :=
      (universalStrongAbsorberTower_stepMap_spec n).toMeetEmbedding.edge_iff
        a b c hab hbc hc
    exact h.symm

/-- The genuine selected strong absorber target tower acquires
eventually fixed literal finite EDGE prefixes if each fixed old
vertex has a horizon-uniform future rank bound. The unbounded
finite target frame sizes have already been proved without
conditional assumptions. -/
theorem selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    EventuallyFixedEdgePrefix
      selectedAbsorberFiniteEdgeTower.size
      selectedAbsorberFiniteEdgeTower.step := by
  let T := selectedAbsorberFiniteOrderTower
  have hUnbounded : ∀ r : Nat, ∃ n : Nat, r < T.size n := by
    intro r
    simpa only [T, selectedAbsorberFiniteOrderTower] using
      universalStrongAbsorberTower_unbounded_frame r
  have hSizes : ∀ r : Nat, ∃ n : Nat, r ≤ T.size n := by
    intro r
    obtain ⟨n,hn⟩ := hUnbounded r
    exact ⟨n,Nat.le_of_lt hn⟩
  have hFix : ∀ r : Nat, ∃ N : Nat,
      ∀ k u : Nat, u < r → T.step (N+k) u = u :=
    fun r => T.exists_eventually_fixed_initial_segments
      hb hUnbounded r
  change EventuallyFixedEdgePrefix T.size T.step
  exact eventuallyFixedEdgePrefix_of_monotone_size_and_frozen_prefix
    T.size T.step T.size_mono hSizes hFix

/-- ACTUAL selected finite absorber targets possess one
countable ordered edge/nonedge relation conditionally on bounded
future ranks. Every literal finite prefix agrees with ALL
sufficiently late full finite targets on both edges and nonedges.

The conditional input is exactly the unproved selected-rank
estimate; this does not promote the edge table to RoleDiary. -/
theorem exists_selectedAbsorber_countable_edge_table_of_boundedRanks
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    ∃ K : Ordered3Graph Nat,
      (∀ a b c : Nat, K.edge a b c → a < b ∧ b < c) ∧
      (∀ r : Nat, ∃ N : Nat, ∀ m : Nat, N ≤ m →
        r ≤ (universalStrongAbsorberTower m).bound ∧
        ∀ a b c : Nat, a < b → b < c → c < r →
          (K.edge a b c ↔
            (universalStrongAbsorberTower m).graph.edge a b c)) := by
  let T := selectedAbsorberFiniteEdgeTower
  have hp : EventuallyFixedEdgePrefix T.size T.step :=
    selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb
  refine ⟨T.limitGraph hp, ?_, ?_⟩
  · intro a b c he
    exact T.limitGraph_edge_ordered hp a b c he
  · intro r
    obtain ⟨N,hN⟩ := T.exists_stable_limit_edge_front hp r
    refine ⟨N, ?_⟩
    intro m hm
    simpa only [T, selectedAbsorberFiniteEdgeTower] using hN m hm

end DiaryLeafPriority
end ThreeUniformDiaries
