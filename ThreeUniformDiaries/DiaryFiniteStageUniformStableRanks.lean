import ThreeUniformDiaries.DiaryFiniteStageInducedIntoConditionalEdgeLimit

/-!
# Track B: uniform stabilization of every old finite absorber stage

The existing selected-tower theorem gives stabilization of each old
vertex separately, conditional on the still-UNPROVED forward-rank bound.
Because each true source frame is finite, these stabilization
thresholds admit ONE common horizon, and every subsequent selected
transition literally fixes the entire stabilized image.

This is a finite-stage stabilization argument; it neither assumes
literal initial-segment extension of finite full diaries, nor claims
that the actual selected tower has bounded forward ranks. The uniform
horizon will permit one finite stage to transfer ALL old roles, edges,
nonedges, capped numerical meets and split witnesses simultaneously.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteOrderTransitionTower

/-- One common stabilization horizon exists for ALL genuine old
vertices below an arbitrary finite source cut. No compactness or
infinite diagonal argument is involved. -/
theorem exists_uniform_stableRank_on_initialSegment
    (T : FiniteOrderTransitionTower) (hb : T.BoundedRanks)
    (n r : Nat) :
    r ≤ T.size n →
    ∃ K : Nat, ∀ k : Nat, K ≤ k →
      ∀ u : Nat, u < r →
        T.forward n k u = T.stableRank hb n u := by
  induction r with
  | zero =>
      intro _
      refine ⟨0, ?_⟩
      intro k hk u hu
      omega
  | succ r ih =>
      intro hr
      obtain ⟨K₀,h₀⟩ := ih (by omega)
      have hFrame : r < T.size n := by omega
      obtain ⟨K₁,h₁⟩ := T.stableRank_spec hb n r hFrame
      refine ⟨max K₀ K₁, ?_⟩
      intro k hk u hu
      by_cases huSmall : u < r
      · exact h₀ k (le_trans (le_max_left _ _) hk) u huSmall
      · have heq : u = r := by omega
        subst u
        exact h₁ k (le_trans (le_max_right _ _) hk)

/-- Specialize to the entire genuine finite source frame, including
all old markers, leaves, split nodes and witness tuples. -/
theorem exists_uniform_stableRank_on_frame
    (T : FiniteOrderTransitionTower) (hb : T.BoundedRanks)
    (n : Nat) :
    ∃ K : Nat, ∀ k : Nat, K ≤ k →
      ∀ u : Nat, u < T.size n →
        T.forward n k u = T.stableRank hb n u := by
  exact T.exists_uniform_stableRank_on_initialSegment
    hb n (T.size n) (le_refl _)

/-- Starting at ONE late horizon, all subsequent selected steps
literally fix the entire canonical stabilized image of an old
finite frame. A finite source need not have occupied a literal
prefix of any of those later frames. -/
theorem exists_eventually_fixed_stableRank_frame
    (T : FiniteOrderTransitionTower) (hb : T.BoundedRanks)
    (n : Nat) :
    ∃ K : Nat, ∀ k u : Nat, u < T.size n →
      T.step (n+K+k) (T.stableRank hb n u) =
        T.stableRank hb n u := by
  obtain ⟨K,hK⟩ := T.exists_uniform_stableRank_on_frame hb n
  refine ⟨K, ?_⟩
  intro k u hu
  have hAt : T.forward n (K+k) u =
      T.stableRank hb n u := hK (K+k) (by omega) u hu
  have hNext : T.forward n ((K+k)+1) u =
      T.stableRank hb n u := hK ((K+k)+1) (by omega) u hu
  have hStep := T.forward_succ n (K+k) u
  rw [hAt,hNext] at hStep
  have hIndex : n+(K+k) = n+K+k := by omega
  simpa only [hIndex] using hStep.symm

end FiniteOrderTransitionTower

/-- The exact, already selected finite strong-absorber tower has
one common stabilization threshold for all vertices of any fixed
old finite target stage, IF its forward ranks are bounded. -/
theorem selectedAbsorberTower_uniformFiniteStageStableRanks
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (n : Nat) :
    ∃ K : Nat, ∀ k : Nat, K ≤ k →
      ∀ u : Nat, u < (universalStrongAbsorberTower n).bound →
        universalStrongAbsorberTower_forwardMap n k u =
          selectedAbsorberFiniteOrderTower.stableRank hb n u := by
  obtain ⟨K,hK⟩ :=
    selectedAbsorberFiniteOrderTower.exists_uniform_stableRank_on_frame hb n
  refine ⟨K, ?_⟩
  intro k hk u hu
  have h := hK k hk u hu
  simpa only [selectedAbsorberFiniteOrderTower_forward_eq] using h

end DiaryLeafPriority
end ThreeUniformDiaries
