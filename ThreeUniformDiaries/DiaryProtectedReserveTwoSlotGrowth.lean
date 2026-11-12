import ThreeUniformDiaries.DiaryProtectedReservePermanentTail
import ThreeUniformDiaries.DiaryFiniteOrderTowerEventuallyFixedPrefix
import Lean.Elab.Tactic.Omega

/-!
# Track B: any protected-reserve absorber tower grows by at least two vertices at EVERY step

The previously verified selected finite absorber reserve interface
requires each old full target frame to embed INSIDE the next
protected cut, and every protected cut to be a proper subset of the
current finite full diary frame. It follows that EVERY selected
successor has strictly larger frame size.

The finite no-literal-full-diary-end-extension theorem sharpens this:
in a proper successor extension the LAST old frame vertex must
move to rank at least old-size. The next protected cut is strictly
after this image, while the next frame leaves a genuine terminal
leaf outside that cut. Thus TWO new numerical slots are required
at EACH step, not merely infinitely many steps:
    oldBound + 1 <= nextProtectedCut < nextBound,
    oldBound + 2 <= nextBound.

These are NECESSARY conditions of the hypothetical reserve structure.
This does NOT construct such a structure or prove bounded ranks of
the arbitrary selected absorber tower.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace SelectedAbsorberProtectedReserve

/-- Capturing the ENTIRE old frame in a PROPER next protected
prefix forces strict frame growth at EVERY selected successor
stage, even where the arbitrary chosen tower might otherwise
have had equal-size stages. -/
theorem strict_growth_every_step
    {r : Nat → Nat} (H : SelectedAbsorberProtectedReserve r)
    (n : Nat) :
    (universalStrongAbsorberTower n).bound <
      (universalStrongAbsorberTower (n+1)).bound := by
  have hOld : (universalStrongAbsorberTower n).bound ≤ r (n+1) :=
    H.prior_frame_le_next_cut n
  have hNew : r (n+1) <
      (universalStrongAbsorberTower (n+1)).bound :=
    H.cut_strict_every_stage (n+1)
  omega

/-- The maximum old image must be STRICTLY beyond the old
finite frame's final rank in every proper selected extension.
Otherwise the old final rank is fixed; finite-order rigidity
then fixes the entire full finite diary, contradicting the
verified no-proper-literal-full-diary extension theorem. -/
theorem last_old_rank_must_move_past_old_frame
    (n : Nat)
    (hGrow :
      (universalStrongAbsorberTower n).bound <
        (universalStrongAbsorberTower (n+1)).bound) :
    (universalStrongAbsorberTower n).bound ≤
      universalStrongAbsorberTower_stepMap n
        ((universalStrongAbsorberTower n).bound-1) := by
  let T := selectedAbsorberFiniteOrderTower
  let b := (universalStrongAbsorberTower n).bound
  have hFour : 4 ≤ b := by
    have h := T.size_mono 0 n (Nat.zero_le n)
    change 4 ≤ b at h
    exact h
  have hLast : b-1 < T.size n := by
    dsimp [b,T,selectedAbsorberFiniteOrderTower]
    omega
  have hLower := T.step_ge_index n (b-1) hLast
  have hMoveLast : T.step n (b-1) ≠ b-1 := by
    intro hLastFixed
    obtain ⟨u,_hu3,hu,hMoved⟩ :=
      selectedAbsorberTower_properGrowth_moves_old_rank n hGrow
    have huBefore : u ≤ b-1 := by omega
    have hFixedU :=
      T.step_fixed_below n (b-1) hLast hLastFixed u huBefore
    apply hMoved
    simpa only [T,selectedAbsorberFiniteOrderTower] using hFixedU
  have hGreater : b ≤ T.step n (b-1) := by omega
  simpa only [T,selectedAbsorberFiniteOrderTower,b] using hGreater

/-- A protected-reserve successor needs TWO genuinely new
numerical positions. The next protected cut includes one
new position beyond all old images; a further new final leaf
remains outside that cut for the following stage. -/
theorem two_fresh_positions_each_step
    {r : Nat → Nat} (H : SelectedAbsorberProtectedReserve r)
    (n : Nat) :
    (universalStrongAbsorberTower n).bound + 1 ≤ r (n+1) ∧
    (universalStrongAbsorberTower n).bound + 2 ≤
      (universalStrongAbsorberTower (n+1)).bound := by
  have hGrow := H.strict_growth_every_step n
  let b := (universalStrongAbsorberTower n).bound
  have hFour : 4 ≤ b := by
    have h := selectedAbsorberFiniteOrderTower.size_mono
      0 n (Nat.zero_le n)
    change 4 ≤ b at h
    exact h
  have hLast : b-1 < (universalStrongAbsorberTower n).bound := by
    dsimp [b]
    omega
  have hMovedMax :
      b ≤ universalStrongAbsorberTower_stepMap n (b-1) := by
    exact last_old_rank_must_move_past_old_frame n hGrow
  have hReserve : universalStrongAbsorberTower_stepMap n (b-1) <
      r (n+1) := H.reserves_old_images n (b-1) hLast
  have hProper : r (n+1) <
      (universalStrongAbsorberTower (n+1)).bound :=
    H.cut_strict_every_stage (n+1)
  constructor <;> dsimp [b] at * <;> omega

end SelectedAbsorberProtectedReserve
end DiaryLeafPriority
end ThreeUniformDiaries
