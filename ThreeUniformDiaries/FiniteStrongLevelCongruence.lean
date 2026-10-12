import ThreeUniformDiaries.FiniteStrongRootLevel

/-!
# A finite geometric strong picture depends only on its finite heights

The original finite strong-tree data uses an infinite function
`f : Nat → Nat` as a convenient selected-level map, although a
height-(k+1) picture only refers to the values f(0),...,f(k).
The extra tail values are mathematically irrelevant.

This precise congruence lemma is needed to replace arbitrary
realizer-dependent level functions by the intrinsic finite-height
code of a scalar Milliken approximation, before defining the
last-vertex F_I colour on the genuine finite approximation.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Equality of the first k+1 level-map values preserves every
field of a genuine finite strong picture, without assumptions on
the arbitrary continuation beyond k. -/
theorem finiteStrongPicture_congr_finite_levels
    {S : Set CoordNode} {f g : Nat → Nat}
    {k : Nat} {root : CoordNode}
    (hS : FiniteStrongPicture S f k root)
    (heq : ∀ i : Nat, i ≤ k → f i = g i) :
    FiniteStrongPicture S g k root := by
  obtain ⟨hfinite, hmeet, hroot, hrootle,
    hlevels, hall, hchildren⟩ := hS
  refine ⟨hfinite, hmeet, hroot, hrootle, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hik, hlevel⟩ := hlevels x hx
    exact ⟨i, hik, by rw [← heq i hik]; exact hlevel⟩
  · intro i hik
    obtain ⟨x, hx, hlevel⟩ := hall i hik
    exact ⟨x, hx, by rw [← heq i hik]; exact hlevel⟩
  · intro i hik p hp hpLevel t hpt
    have hi : i ≤ k := Nat.le_of_lt hik
    have hi1 : i + 1 ≤ k := by omega
    have hpF : level p = f i := by
      rw [heq i hi]
      exact hpLevel
    obtain ⟨z, ⟨hz, hzLevel, htz⟩, hunique⟩ :=
      hchildren i hik p hp hpF t hpt
    refine ⟨z, ⟨hz, ?_, htz⟩, ?_⟩
    · rw [← heq (i + 1) hi1]
      exact hzLevel
    · intro w ⟨hw, hwLevel, htw⟩
      apply hunique w
      refine ⟨hw, ?_, htw⟩
      rw [heq (i + 1) hi1]
      exact hwLevel

/-- Finite geometric root levels are also invariant under changing
the unused tail of the selected height function. -/
theorem finiteStrongPicture_root_level_congr
    {S : Set CoordNode} {f g : Nat → Nat}
    {k : Nat} {root : CoordNode}
    (hS : FiniteStrongPicture S f k root)
    (heq : ∀ i : Nat, i ≤ k → f i = g i)
    (hf : StrictMono f) :
    level root = g 0 := by
  have hroot := finiteStrongPicture_root_level hS hf
  rw [← heq 0 (Nat.zero_le k)]
  exact hroot

end CoordNode
end ThreeUniformDiaries
