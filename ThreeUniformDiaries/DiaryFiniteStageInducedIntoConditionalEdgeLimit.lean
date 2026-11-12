import ThreeUniformDiaries.DiarySelectedAbsorberConditionalEdgeColimit
import Lean.Elab.Tactic.Omega

/-!
# Track B: finite absorber stages embed inducedly into the conditional edge limit

The previous selected-tower colimit theorem gives eventually literal finite
edge/nonedge prefixes, assuming bounded ranks. This module proves a different
piece of information: every ORIGINAL finite target stage has a coherent
strictly increasing induced embedding into that limit.

The embedding is given by the eventual numerical rank of each old vertex.
We prove inducedness for edges AND nonedges, using (i) exact bounded
successor embeddings, (ii) eventual rank stabilization, and (iii) literal
finite-prefix edge stabilization. No full RoleDiary limit or bounded-rank
existence is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

namespace FiniteOrderTransitionTower

/-- Canonical eventual numerical rank of an old vertex in a bounded-rank
finite-order tower. Values outside the actual stage frame are irrelevant. -/
noncomputable def stableRank (T : FiniteOrderTransitionTower)
    (hb : T.BoundedRanks) (n u : Nat) : Nat :=
  if hu : u < T.size n then
    Classical.choose (T.exists_stable_forward_rank hb n u hu)
  else 0

/-- Every actual stage vertex has its chosen stable rank at all sufficiently
late horizons. This uses the TRUE selected forward maps. -/
theorem stableRank_spec (T : FiniteOrderTransitionTower)
    (hb : T.BoundedRanks) (n u : Nat) (hu : u < T.size n) :
    ∃ K : Nat, ∀ k : Nat, K ≤ k →
      T.forward n k u = T.stableRank hb n u := by
  have h :=
    Classical.choose_spec (T.exists_stable_forward_rank hb n u hu)
  simpa only [stableRank, dif_pos hu] using h

/-- Eventual ranks are strictly increasing on every genuine finite frame;
strictness is inherited at one sufficiently late common horizon. -/
theorem stableRank_strict (T : FiniteOrderTransitionTower)
    (hb : T.BoundedRanks) (n u v : Nat)
    (huv : u < v) (hv : v < T.size n) :
    T.stableRank hb n u < T.stableRank hb n v := by
  have hu : u < T.size n := by omega
  obtain ⟨Ku,hKu⟩ := T.stableRank_spec hb n u hu
  obtain ⟨Kv,hKv⟩ := T.stableRank_spec hb n v hv
  have h := T.forward_strict n (max Ku Kv) u v huv hv
  rw [hKu (max Ku Kv) (le_max_left _ _),
      hKv (max Ku Kv) (le_max_right _ _)] at h
  exact h


/-- The stable-rank maps form a coherent cocone over the selected
finite-frame transitions; this is stronger than independent embeddings
of the separate finite stages. -/
theorem stableRank_step (T : FiniteOrderTransitionTower)
    (hb : T.BoundedRanks) (n u : Nat) (hu : u < T.size n) :
    T.stableRank hb (n+1) (T.step n u) =
      T.stableRank hb n u := by
  obtain ⟨Kold,hOld⟩ := T.stableRank_spec hb n u hu
  obtain ⟨Knew,hNew⟩ :=
    T.stableRank_spec hb (n+1) (T.step n u)
      (T.step_bound n u hu)
  let k : Nat := max Kold Knew
  have h1 := hOld (k+1) (by dsimp [k]; omega)
  have h2 := hNew k (by dsimp [k]; omega)
  rw [T.forward_shift n k u, h2] at h1
  exact h1

/-- Naturality of the eventual-rank map with EVERY finite-horizon
composite, not just a single successor. -/
theorem stableRank_forward (T : FiniteOrderTransitionTower)
    (hb : T.BoundedRanks) (n k u : Nat) (hu : u < T.size n) :
    T.stableRank hb (n+k) (T.forward n k u) =
      T.stableRank hb n u := by
  induction k with
  | zero =>
      simp only [Nat.add_zero, forward_zero]
  | succ k ih =>
      have hStep :=
        T.stableRank_step hb (n+k) (T.forward n k u)
          (T.forward_bound n k u hu)
      have h := hStep.trans ih
      simpa only [Nat.add_succ, forward_succ] using h

end FiniteOrderTransitionTower

namespace FiniteInducedEdgeTower

/-- Complete inducedness for any selected finite horizon, with the
order-tower maps providing their honest finite-frame range and order bounds.
The iff explicitly reflects nonedges. -/
theorem edge_iff_forward
    (E : FiniteInducedEdgeTower) (T : FiniteOrderTransitionTower)
    (hSize : E.size = T.size) (hStep : E.step = T.step)
    (n k a b c : Nat)
    (hab : a < b) (hbc : b < c) (hc : c < E.size n) :
    (E.edge n a b c ↔
      E.edge (n+k) (T.forward n k a)
        (T.forward n k b) (T.forward n k c)) := by
  induction k with
  | zero =>
      simp only [Nat.add_zero, FiniteOrderTransitionTower.forward_zero]
  | succ k ih =>
      have hcT : c < T.size n := by
        rw [← hSize]
        exact hc
      have hbT : b < T.size n := by omega
      have habF : T.forward n k a < T.forward n k b :=
        T.forward_strict n k a b hab hbT
      have hbcF : T.forward n k b < T.forward n k c :=
        T.forward_strict n k b c hbc hcT
      have hcFrame : T.forward n k c < E.size (n+k) := by
        rw [hSize]
        exact T.forward_bound n k c hcT
      have hNext :=
        E.step_induced (n+k)
          (T.forward n k a) (T.forward n k b) (T.forward n k c)
          habF hbcF hcFrame
      rw [hStep] at hNext
      have hAll := ih.trans hNext
      simpa only [Nat.add_succ, FiniteOrderTransitionTower.forward_succ]
        using hAll

/-- Main generic bridge: stabilized numerical ranks embed EACH finite
stage as an induced ordered 3-graph into the canonical prefix limit. The
source stages are not required to be literal initial segments of later
stages. -/
theorem edge_iff_limit_of_stableRanks
    (E : FiniteInducedEdgeTower) (T : FiniteOrderTransitionTower)
    (hSize : E.size = T.size) (hStep : E.step = T.step)
    (hb : T.BoundedRanks)
    (hp : EventuallyFixedEdgePrefix E.size E.step)
    (n a b c : Nat)
    (hab : a < b) (hbc : b < c) (hc : c < E.size n) :
    E.edge n a b c ↔
      (E.limitGraph hp).edge
        (T.stableRank hb n a) (T.stableRank hb n b)
        (T.stableRank hb n c) := by
  let f : Nat → Nat := T.stableRank hb n
  have hcT : c < T.size n := by
    rw [← hSize]
    exact hc
  have hbT : b < T.size n := by omega
  have haT : a < T.size n := by omega
  obtain ⟨Ka,hKa⟩ := T.stableRank_spec hb n a haT
  obtain ⟨Kb,hKb⟩ := T.stableRank_spec hb n b hbT
  obtain ⟨Kc,hKc⟩ := T.stableRank_spec hb n c hcT
  have habF : f a < f b :=
    T.stableRank_strict hb n a b hab hbT
  have hbcF : f b < f c :=
    T.stableRank_strict hb n b c hbc hcT
  let q : Nat := f c + 1
  let j : Nat :=
    max (n + max (max Ka Kb) Kc) (edgePrefixCutoff hp q)
  let k : Nat := j - n
  have hMain : n + max (max Ka Kb) Kc ≤ j := le_max_left _ _
  have hCut : edgePrefixCutoff hp q ≤ j := le_max_right _ _
  have hn : n ≤ j := by omega
  have hK : max (max Ka Kb) Kc ≤ k := by
    dsimp [k]
    omega
  have hkA : Ka ≤ k :=
    le_trans (le_trans (le_max_left Ka Kb)
      (le_max_left (max Ka Kb) Kc)) hK
  have hkB : Kb ≤ k :=
    le_trans (le_trans (le_max_right Ka Kb)
      (le_max_left (max Ka Kb) Kc)) hK
  have hkC : Kc ≤ k :=
    le_trans (le_max_right (max Ka Kb) Kc) hK
  have hj : n + k = j := by
    dsimp [k]
    omega
  have hAtJ : E.edge n a b c ↔ E.edge j (f a) (f b) (f c) := by
    have hForward :=
      E.edge_iff_forward T hSize hStep n k a b c hab hbc hc
    have hA := hKa k hkA
    have hB := hKb k hkB
    have hC := hKc k hkC
    simpa only [hj, hA, hB, hC] using hForward
  have hAtLimit :=
    E.limitGraph_edge_iff_late hp q j hCut
      (f a) (f b) (f c) habF hbcF
      (by dsimp [q]; omega)
  exact hAtJ.trans hAtLimit.symm

end FiniteInducedEdgeTower

/-- Every actual selected finite full strong-absorber target is present
inducedly in the selected countable edge-table limit, provided that the
selected tower has bounded forward ranks.

This is an edge/nonedge embedding theorem ONLY. It does not assert
that the limit satisfies V1/V2 split witnesses, V3, or S1/S2, nor that
the bounded-rank hypothesis holds for the selected absorbers. -/
theorem selectedAbsorberFiniteStage_induced_in_conditionalEdgeLimit
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (n a b c : Nat)
    (hab : a < b) (hbc : b < c)
    (hc : c < (universalStrongAbsorberTower n).bound) :
    (selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)).edge
      (selectedAbsorberFiniteOrderTower.stableRank hb n a)
      (selectedAbsorberFiniteOrderTower.stableRank hb n b)
      (selectedAbsorberFiniteOrderTower.stableRank hb n c) ↔
    (universalStrongAbsorberTower n).graph.edge a b c := by
  have h :=
    FiniteInducedEdgeTower.edge_iff_limit_of_stableRanks
      selectedAbsorberFiniteEdgeTower selectedAbsorberFiniteOrderTower
      (by rfl) (by rfl) hb
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
      n a b c hab hbc hc
  exact h.symm

end DiaryLeafPriority
end ThreeUniformDiaries
