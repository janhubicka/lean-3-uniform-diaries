import Mathlib

/-!
# A unique binary branch following prefix-dependent flip instructions

The published flip-absorption argument ends during an induction
choosing the flip of A that compensates for a prescribed flip of
the universal tree B. At stage n the next bit depends on the
previous prefix of n choices.

This purely finite-branch-recursion lemma constructs the unique
infinite Boolean sequence satisfying ANY such triangular
system of equations. The step function can inspect the earlier
n bits but cannot depend on its own bit or later choices.

This discharges the abstract combinatorial induction in the
second formulation of the flip property. It does not prove
that the target flip actually induces the required step
function or that the resulting embedding preserves type meets.
Those are geometric pullback obligations.
-/

namespace ThreeUniformDiaries
namespace FlipGuidedBranch

/-- The next bit of a guided branch is calculated from its
strictly shorter prefix. Lean's well-founded recursion makes
the dependency on prior bits explicit and avoids any choice
of an infinite branch by compactness. -/
def guidedBit
    (step : ∀ n : Nat, (Fin n → Bool) → Bool)
    (n : Nat) : Bool :=
  step n (fun i : Fin n => guidedBit step i.val)
termination_by n
decreasing_by exact i.isLt

/-- The constructed branch obeys its defining prefix equation. -/
theorem guidedBit_step
    (step : ∀ n : Nat, (Fin n → Bool) → Bool) (n : Nat) :
    guidedBit step n =
      step n (fun i : Fin n => guidedBit step i.val) := by
  rw [guidedBit]

/-- Two infinite branches satisfying the same prefix-dependent
instructions are equal. No branching/compactness hypothesis
is needed beyond well-foundedness of Nat. -/
theorem guided_branch_unique
    (step : ∀ n : Nat, (Fin n → Bool) → Bool)
    (p q : Nat → Bool)
    (hp : ∀ n, p n = step n (fun i : Fin n => p i.val))
    (hq : ∀ n, q n = step n (fun i : Fin n => q i.val)) :
    p = q := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      calc
        p n = step n (fun i : Fin n => p i.val) := hp n
        _ = step n (fun i : Fin n => q i.val) := by
          congr 1
          funext i
          exact ih i.val i.isLt
        _ = q n := (hq n).symm

/-- The complete self-contained existence-and-uniqueness API
for a binary prefix recursion. -/
theorem existsUnique_guided_branch
    (step : ∀ n : Nat, (Fin n → Bool) → Bool) :
    ∃! p : Nat → Bool,
      ∀ n, p n = step n (fun i : Fin n => p i.val) := by
  refine ⟨guidedBit step, guidedBit_step step, ?_⟩
  intro q hq
  exact guided_branch_unique step q (guidedBit step)
    hq (guidedBit_step step)

end FlipGuidedBranch
end ThreeUniformDiaries
