import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Order preservation from the pre-embedding split intervals

After choosing all leaf images from an increasing induced target
copy f, the pre-embedding assigns the three initial markers
their original values and chooses the image of each non-leaf
split i in the interval

    f (i-1) < image i ≤ f i.

This module proves that the resulting total diary map is strictly
increasing, independently of how each witness was chosen. This is
a numerical consequence of disjoint predecessor intervals, NOT a
claim that type meets are globally preserved through skipped levels.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any strictly increasing map of the natural numbers dominates
the identity; this controls the initial three marker positions. -/
theorem strictMono_nat_ge_id (f : Nat → Nat)
    (hf : StrictMono f) (n : Nat) : n ≤ f n := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hstep : f n < f (n+1) := hf (by omega)
      omega

/-- Disjoint predecessor intervals force the complete extended
map to be strictly increasing, provided it fixes the three markers.
The original target leaf map may have arbitrary gaps. -/
theorem strictMono_of_preembedding_intervals
    (f g : Nat → Nat) (hf : StrictMono f)
    (hzero : g 0 = 0) (hone : g 1 = 1) (htwo : g 2 = 2)
    (hinterval : ∀ i, 3 ≤ i →
        f (i-1) < g i ∧ g i ≤ f i) :
    StrictMono g := by
  have hsmall : ∀ n : Nat, n < 3 → g n = n := by
    intro n hn
    by_cases hz : n = 0
    · subst n
      exact hzero
    by_cases ho : n = 1
    · subst n
      exact hone
    have ht : n = 2 := by omega
    subst n
    exact htwo
  intro i j hij
  by_cases hi : i < 3
  · by_cases hj : j < 3
    · rw [hsmall i hi, hsmall j hj]
      exact hij
    · have hbig : 3 ≤ j := by omega
      have hpred : 2 ≤ j-1 := by omega
      have hfLower := strictMono_nat_ge_id f hf (j-1)
      have hGi : g i ≤ 2 := by rw [hsmall i hi]; omega
      have hGj := (hinterval j hbig).1
      omega
  · have hiBig : 3 ≤ i := by omega
    have hjBig : 3 ≤ j := by omega
    have hupper := (hinterval i hiBig).2
    have hlower := (hinterval j hjBig).1
    have hmon : f i ≤ f (j-1) :=
      hf.monotone (by omega)
    omega

/-- The V-role partition of a complete diary reduces the global
strict monotonicity check to the three separately established
leaf, one-split and two-split placement conditions. -/
theorem strictMono_of_diary_role_intervals
    {H : Ordered3Graph Nat} (D : RoleDiary H)
    (f g : Nat → Nat) (hf : StrictMono f)
    (hzero : g 0 = 0) (hone : g 1 = 1) (htwo : g 2 = 2)
    (hleaf : ∀ i, 3 ≤ i → IsLeaf H i → g i = f i)
    (honeSplit : ∀ i, IsOneSplit H i →
      f (i-1) < g i ∧ g i ≤ f i)
    (htwoSplit : ∀ i, IsTwoSplit H i →
      f (i-1) < g i ∧ g i ≤ f i) :
    StrictMono g := by
  apply strictMono_of_preembedding_intervals f g hf hzero hone htwo
  intro i hi
  rcases D.role_valid i hi with hLeaf | hOne | hTwo
  · rw [hleaf i hi hLeaf]
    have hp : i-1 < i := by omega
    exact ⟨hf hp, le_rfl⟩
  · exact honeSplit i hOne
  · exact htwoSplit i hTwo

end DiaryLeafPriority
end ThreeUniformDiaries
