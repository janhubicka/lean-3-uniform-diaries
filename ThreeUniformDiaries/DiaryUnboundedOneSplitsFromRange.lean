import ThreeUniformDiaries.DiarySingletonColourCofinalCone
import ThreeUniformDiaries.DiaryMonochromaticLeafMeetObstruction

/-!
# High one-split witnesses inside any injected range of genuine diary leaves

Every injected infinite family of genuine target leaves produces genuine
one-split meets above any numerical bound. No order assumption on the
external map or genericity of the leaf reduct is needed.
English proof and adversarial review: janhubicka/3-uniform-diaries #267.
This does not realize a fixed full mixed type or persistent successor.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For any target bound B and input-index threshold N, a genuine
one-split meet at least B is witnessed by a pair of injected leaves
with input indices N <= i < j, even if F is not increasing. -/
theorem RoleDiary.exists_arbitrarily_high_oneSplit_in_injective_leaf_range
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : Nat → Nat)
    (hInj : Function.Injective F)
    (hLeaf : ∀ i : Nat, IsLeaf K (F i))
    (B N : Nat) :
    ∃ i j : Nat,
      N ≤ i ∧ i < j ∧
      B ≤ K.oneMeetLevel (F i) (F j) ∧
      IsOneSplit K (K.oneMeetLevel (F i) (F j)) := by
  classical
  obtain ⟨p, hRec⟩ := exists_cofinal_existing_singletonColour K B F
  obtain ⟨M, hLarge⟩ := injective_nat_eventually_above_bound F hInj B
  obtain ⟨i, hi, hpi⟩ := hRec (max N M)
  obtain ⟨j, hj, hpj⟩ := hRec (i + 1)
  have hNi : N ≤ i := (le_max_left N M).trans hi
  have hMi : M ≤ i := (le_max_right N M).trans hi
  have hij : i < j := by omega
  have hBj : B ≤ F j := by
    have h := hLarge j (le_trans hMi (le_of_lt hij))
    omega
  have hBi : B ≤ F i := by
    have h := hLarge i hMi
    omega
  have hSame :
      DiaryLowerBoundColors.singletonColour K B (F i) =
        DiaryLowerBoundColors.singletonColour K B (F j) :=
    hpi.trans hpj.symm
  have hMeet : B ≤ K.oneMeetLevel (F i) (F j) :=
    equal_singletonColour_forces_oneMeet_ge_cut
      K B (F i) (F j) hBi hBj hSame
  have hNe : F i ≠ F j := by
    intro h
    exact (ne_of_lt hij) (hInj h)
  exact ⟨i, j, hNi, hij, hMeet,
    DK.singleton_meets (F i) (F j) (hLeaf i) (hLeaf j) hNe⟩

end DiaryLeafPriority
end ThreeUniformDiaries
