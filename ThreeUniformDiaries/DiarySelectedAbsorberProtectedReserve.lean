import ThreeUniformDiaries.DiarySelectedTowerUnavoidableMotion
import ThreeUniformDiaries.DiaryFiniteOrderTowerEventualFrontCapture
import ThreeUniformDiaries.DiaryGrowingFrozenPrefixEscapeAndReserve

/-!
# Track B: exact finite-reservation objective for the selected strong absorber

We isolate a concrete, stage-by-stage strengthening that would finish
the still OPEN bounded-ranks construction. Every genuine finite source
vertex must lie below the NEXT protected cut after its selected
embedding, and subsequent selected steps must fix previously protected
cuts. A finite full diary cannot be literally end-extended; hence the
protected cut may not equal the whole old frame at a growing step.

This is a DEFINITION + CONDITIONAL CONSEQUENCES, not an existence
theorem for those cuts. The previously proved finite absorber-extension
theorem only chooses an unspecified bounded embedding and gives NO
control of either the selected old ranks or a protected prefix.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A concrete protection scheme on the ACTUAL selected finite
strong-absorber tower. The protected prefix lies in its TRUE finite
frame, grows monotonically, remains fixed by the selected transition,
and captures the entire old finite frame by the next protected cut.

The existence of such an r is an OPEN finite relative-extension
problem; this structure must not be silently instantiated. -/
structure SelectedAbsorberProtectedReserve (r : Nat → Nat) : Prop where
  within_frame : ∀ n : Nat, r n ≤ (universalStrongAbsorberTower n).bound
  monotone_cut : Monotone r
  fixes_cut : ∀ n u : Nat, u < r n →
    universalStrongAbsorberTower_stepMap n u = u
  reserves_old_images : ∀ n u : Nat,
    u < (universalStrongAbsorberTower n).bound →
      universalStrongAbsorberTower_stepMap n u < r (n+1)

namespace SelectedAbsorberProtectedReserve

/-- The finite one-step reserve condition is already enough to
give horizon-uniform bounds for every actual old vertex. No
global monotonicity of the total Nat successor maps is assumed. -/
theorem boundedRanks
    {r : Nat → Nat} (H : SelectedAbsorberProtectedReserve r) :
    selectedAbsorberFiniteOrderTower.BoundedRanks := by
  exact selectedAbsorberFiniteOrderTower.boundedRanks_of_reserved_cuts
    r H.monotone_cut H.reserves_old_images H.fixes_cut

/-- The protected cuts MUST be unbounded: each stage old vertex
is below the next reserve and finite selected rank maps cannot
decrease a true old vertex's numerical position. -/
theorem cut_unbounded
    {r : Nat → Nat} (H : SelectedAbsorberProtectedReserve r) :
    ∀ R : Nat, ∃ j : Nat, R < r j := by
  intro R
  obtain ⟨n,hLarge⟩ := universalStrongAbsorberTower_unbounded_frame R
  have hu : R < selectedAbsorberFiniteOrderTower.size n := by
    simpa only [selectedAbsorberFiniteOrderTower] using hLarge
  have hGe := selectedAbsorberFiniteOrderTower.step_ge_index n R hu
  have hReserve := H.reserves_old_images n R hLarge
  exact ⟨n+1, by omega⟩

/-- Whenever the selected finite full diary grows properly, the
current protected prefix CANNOT be the entire current frame.
Otherwise the next selected embedding would contradict the
verified finite no-literal-full-diary-extension theorem. -/
theorem cut_strict_of_properGrowth
    {r : Nat → Nat} (H : SelectedAbsorberProtectedReserve r)
    (n : Nat)
    (hGrow :
      (universalStrongAbsorberTower n).bound <
        (universalStrongAbsorberTower (n+1)).bound) :
    r n < (universalStrongAbsorberTower n).bound := by
  have hWithin := H.within_frame n
  by_contra hNot
  have hEq : r n = (universalStrongAbsorberTower n).bound := by
    omega
  obtain ⟨u,_hu3,hu,hMoved⟩ :=
    selectedAbsorberTower_properGrowth_moves_old_rank n hGrow
  have hFix : universalStrongAbsorberTower_stepMap n u = u :=
    H.fixes_cut n u (by rw [hEq]; exact hu)
  exact hMoved hFix

/-- The current finite frame must fit into the next protected
cut as an ordered set: strict finite-frame embeddings lie at
least at the identity rank, and ALL old images are reserved. -/
theorem prior_frame_le_next_cut
    {r : Nat → Nat} (H : SelectedAbsorberProtectedReserve r)
    (n : Nat) :
    (universalStrongAbsorberTower n).bound ≤ r (n+1) := by
  have hSize := selectedAbsorberFiniteOrderTower.size_mono
    0 n (Nat.zero_le n)
  have hn : 4 ≤ (universalStrongAbsorberTower n).bound := by
    change 4 ≤ (universalStrongAbsorberTower n).bound at hSize
    exact hSize
  let v := (universalStrongAbsorberTower n).bound - 1
  have hv : v < (universalStrongAbsorberTower n).bound := by
    dsimp [v]
    omega
  have hReserve := H.reserves_old_images n v hv
  have hRank : v ≤ universalStrongAbsorberTower_stepMap n v := by
    exact selectedAbsorberFiniteOrderTower.step_ge_index n v hv
  dsimp [v] at *
  omega

/-- The exact controlled-reserve structure would produce a
GENUINE countable full RoleDiary via the previously CI-verified
stable-rank colimit construction. This adds NO new existence
premise beyond the explicitly supplied finite-reservation data. -/
theorem full_countable_diary_of_reserve
    {r : Nat → Nat} (H : SelectedAbsorberProtectedReserve r) :
    RoleDiary
      (selectedAbsorberFiniteEdgeTower.limitGraph
        (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks
          H.boundedRanks)) := by
  exact selectedAbsorberLimit_isRoleDiary_of_boundedRanks H.boundedRanks

end SelectedAbsorberProtectedReserve

/-- Weaker finite-injury criterion: with a supplied nondecreasing
protected cut fixed by all selected transitions, it suffices that
EACH old vertex EVENTUALLY enters that front. The capture horizons
may be different for different old vertices. -/
theorem selectedAbsorberLimit_fullDiary_of_eventualFrontCapture
    (r : Nat → Nat)
    (hMono : Monotone r)
    (hFix : ∀ n u : Nat, u < r n →
      universalStrongAbsorberTower_stepMap n u = u)
    (hCapture : selectedAbsorberFiniteOrderTower.EventualFrontCapture r) :
    RoleDiary
      (selectedAbsorberFiniteEdgeTower.limitGraph
        (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks
          (selectedAbsorberFiniteOrderTower.boundedRanks_of_eventualFrontCapture
            r hMono hFix hCapture))) := by
  exact selectedAbsorberLimit_isRoleDiary_of_boundedRanks
    (selectedAbsorberFiniteOrderTower.boundedRanks_of_eventualFrontCapture
      r hMono hFix hCapture)

/-- Exact cut-level form of the remaining infinite-horizon issue.
Even if a monotone, unbounded, literally frozen front is given,
bounded old ranks are equivalent to EVENTUAL CAPTURE and do NOT
follow from the mere growth of that front. -/
theorem selectedAbsorberTower_boundedRanks_iff_frontCapture
    (r : Nat → Nat)
    (hMono : Monotone r)
    (hUnbounded : ∀ M : Nat, ∃ j : Nat, M < r j)
    (hFixed : ∀ n u : Nat, u < r n →
      universalStrongAbsorberTower_stepMap n u = u) :
    selectedAbsorberFiniteOrderTower.BoundedRanks ↔
      selectedAbsorberFiniteOrderTower.EventualFrontCapture r := by
  exact selectedAbsorberFiniteOrderTower.boundedRanks_iff_eventualFrontCapture
    r hMono hUnbounded hFixed

end DiaryLeafPriority
end ThreeUniformDiaries
