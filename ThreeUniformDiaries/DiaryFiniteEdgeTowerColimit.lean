import ThreeUniformDiaries.AuxTypes
import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Prefix data for a tower of finite initial-frame edge tables.
The protected prefixes eventually cover every finite numerical cut. -/
def EventuallyFixedEdgePrefix
    (size : Nat → Nat) (step : Nat → Nat → Nat) : Prop :=
  ∀ r : Nat, ∃ N : Nat, ∀ m : Nat, N ≤ m →
    r ≤ size m ∧ ∀ u : Nat, u < r → step m u = u

noncomputable def edgePrefixCutoff
    {size : Nat → Nat} {step : Nat → Nat → Nat}
    (h : EventuallyFixedEdgePrefix size step) (r : Nat) : Nat :=
  Classical.choose (h r)

theorem edgePrefixCutoff_spec
    {size : Nat → Nat} {step : Nat → Nat → Nat}
    (h : EventuallyFixedEdgePrefix size step) (r m : Nat)
    (hm : edgePrefixCutoff h r ≤ m) :
    r ≤ size m ∧ ∀ u : Nat, u < r → step m u = u := by
  exact Classical.choose_spec (h r) m hm

/-- An expanding eventually fixed prefix and unbounded monotone
frame sizes together give a single useful strong prefix cutoff. -/
theorem eventuallyFixedEdgePrefix_of_monotone_size_and_frozen_prefix
    (size : Nat → Nat) (step : Nat → Nat → Nat)
    (hSizeMono : ∀ a b : Nat, a ≤ b → size a ≤ size b)
    (hSizeUnbounded : ∀ r : Nat, ∃ n : Nat, r ≤ size n)
    (hFix : ∀ r : Nat, ∃ N : Nat,
      ∀ k u : Nat, u < r → step (N+k) u = u) :
    EventuallyFixedEdgePrefix size step := by
  intro r
  obtain ⟨N₀, hFrozen⟩ := hFix r
  obtain ⟨N₁, hFrame⟩ := hSizeUnbounded r
  refine ⟨max N₀ N₁, ?_⟩
  intro m hm
  have h0 : N₀ ≤ m := le_trans (le_max_left _ _) hm
  have h1 : N₁ ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨le_trans hFrame (hSizeMono N₁ m h1), ?_⟩
  intro u hu
  have hEq : N₀ + (m-N₀) = m := by omega
  simpa only [hEq] using hFrozen (m-N₀) u hu

/-- An induced finite-edge tower. The edge predicate on the unused
Nat tail is irrelevant; only increasing triples in [0,size n) occur. -/
structure FiniteInducedEdgeTower where
  size : Nat → Nat
  step : Nat → Nat → Nat
  edge : Nat → Nat → Nat → Nat → Prop
  edge_ordered : ∀ n a b c, edge n a b c → a < b ∧ b < c
  step_induced : ∀ n a b c : Nat, a < b → b < c → c < size n →
    (edge n a b c ↔ edge (n+1) (step n a) (step n b) (step n c))

namespace FiniteInducedEdgeTower

/-- A canonical limit edge predicate at the cutoff chosen for the
largest coordinate. It is independent of that cutoff, as proved below. -/
noncomputable def limitGraph (T : FiniteInducedEdgeTower)
    (hp : EventuallyFixedEdgePrefix T.size T.step) :
    Ordered3Graph Nat where
  edge a b c := T.edge (edgePrefixCutoff hp (c+1)) a b c

/-- All old increasing triples agree on every horizon beyond a
frozen prefix threshold. This includes nonedges via the iff. -/
theorem edge_stable_after_cut (T : FiniteInducedEdgeTower)
    (hp : EventuallyFixedEdgePrefix T.size T.step)
    (r m : Nat) (hm : edgePrefixCutoff hp r ≤ m)
    (a b c : Nat) (hab : a < b) (hbc : b < c)
    (hc : c < r) :
    (T.edge (edgePrefixCutoff hp r) a b c ↔ T.edge m a b c) := by
  induction m, hm using Nat.le_induction with
  | base => exact Iff.rfl
  | succ m hm ih =>
      have hPref := edgePrefixCutoff_spec hp r m hm
      have hFrame : c < T.size m := by omega
      have hStep := T.step_induced m a b c hab hbc hFrame
      have ha : T.step m a = a := hPref.2 a (by omega)
      have hb : T.step m b = b := hPref.2 b (by omega)
      have hc' : T.step m c = c := hPref.2 c hc
      rw [ha,hb,hc'] at hStep
      exact ih.trans hStep

/-- Any two sufficiently late edge tables agree with the same
literal limit edge table, even when separately chosen cuts differ. -/
theorem limitGraph_edge_iff_late (T : FiniteInducedEdgeTower)
    (hp : EventuallyFixedEdgePrefix T.size T.step)
    (r m : Nat) (hm : edgePrefixCutoff hp r ≤ m)
    (a b c : Nat) (hab : a < b) (hbc : b < c)
    (hc : c < r) :
    (T.limitGraph hp).edge a b c ↔ T.edge m a b c := by
  let j : Nat := max (edgePrefixCutoff hp (c+1)) m
  have hj1 : edgePrefixCutoff hp (c+1) ≤ j := le_max_left _ _
  have hj2 : edgePrefixCutoff hp r ≤ j :=
    le_trans hm (le_max_right _ _)
  have hOne := T.edge_stable_after_cut hp (c+1) j hj1 a b c hab hbc (by omega)
  have hAtJ := T.edge_stable_after_cut hp r j hj2 a b c hab hbc hc
  have hAtM := T.edge_stable_after_cut hp r m hm a b c hab hbc hc
  change T.edge (edgePrefixCutoff hp (c+1)) a b c ↔ T.edge m a b c
  exact hOne.trans (hAtJ.symm.trans hAtM)

/-- Genuine edge support passes to the pointwise countable table. -/
theorem limitGraph_edge_ordered (T : FiniteInducedEdgeTower)
    (hp : EventuallyFixedEdgePrefix T.size T.step)
    (a b c : Nat) (h : (T.limitGraph hp).edge a b c) :
    a < b ∧ b < c := by
  exact T.edge_ordered (edgePrefixCutoff hp (c+1)) a b c h

/-- The complete finite edge/nonedge diagram on EVERY fixed cut
becomes literal at all sufficiently late stages. -/
theorem exists_stable_limit_edge_front (T : FiniteInducedEdgeTower)
    (hp : EventuallyFixedEdgePrefix T.size T.step)
    (r : Nat) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m →
      r ≤ T.size m ∧
      ∀ a b c : Nat, a < b → b < c → c < r →
        ((T.limitGraph hp).edge a b c ↔ T.edge m a b c) := by
  refine ⟨edgePrefixCutoff hp r, ?_⟩
  intro m hm
  refine ⟨(edgePrefixCutoff_spec hp r m hm).1, ?_⟩
  intro a b c hab hbc hc
  exact T.limitGraph_edge_iff_late hp r m hm a b c hab hbc hc

end FiniteInducedEdgeTower
end DiaryLeafPriority
end ThreeUniformDiaries
