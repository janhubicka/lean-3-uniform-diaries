import ThreeUniformDiaries.AuxTypes
import Mathlib

/-!
# Eventual finite avoidance for an arbitrary injective outer embedding

The diary lower-bound argument begins with an embedding f that need
NOT respect the enumeration order. Its injectivity, however, ensures
that only finitely many source vertices map below a fixed bound M.

For a direct finite proof, assign each target value y ≤ M its
(unique, if existing) source preimage, and choose B beyond the
sum of these finitely many candidate preimages. Then every vertex
v ≥ B has f(v) > M. This avoids introducing a false assumption that
f itself is increasing.

The same assertion holds for f composed with any increasing
aux-type-respecting self-embedding, since the composite is injective.
-/

namespace ThreeUniformDiaries
namespace DiaryLowerBoundAvoidance

/-- Every injection Nat -> Nat eventually leaves an arbitrary
initial target interval, without any monotonicity assumption. -/
theorem eventually_above_of_injective
    (F : Nat → Nat) (hF : Function.Injective F) (M : Nat) :
    ∃ B : Nat, ∀ v, B ≤ v → M < F v := by
  classical
  let inverse : Nat → Nat :=
    fun y => if h : ∃ x, F x = y then Classical.choose h else 0
  let B : Nat := (Finset.range (M+1)).sum (fun y => inverse y + 1)
  refine ⟨B, ?_⟩
  intro v hv
  by_contra hn
  have hy : F v ∈ Finset.range (M+1) :=
    Finset.mem_range.mpr (by omega)
  have hinverse : inverse (F v) = v := by
    dsimp [inverse]
    split_ifs with h
    · exact hF (Classical.choose_spec h)
    · exact False.elim (h ⟨v, rfl⟩)
  have hsum : inverse (F v) + 1 ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum
      (f := fun y : Nat => inverse y + 1)
      (fun y hy => Nat.zero_le (inverse y + 1)) hy
  omega

/-- The outer embedding need only be injective. Composing it with
any injective inner map preserves the finite-avoidance property. -/
theorem eventually_above_after_injective_refinement
    (F : Nat → Nat) (hF : Function.Injective F)
    (g : Nat → Nat) (hg : Function.Injective g)
    (M : Nat) :
    ∃ B : Nat, ∀ v, B ≤ v → M < F (g v) := by
  exact eventually_above_of_injective (fun v => F (g v))
    (hF.comp hg) M

end DiaryLowerBoundAvoidance
end ThreeUniformDiaries
