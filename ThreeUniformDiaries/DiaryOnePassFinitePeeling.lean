import Mathlib

/-!
# Finite one-hot refinement blocks in one-pass diary completion

For k+1 nonempty children of a given original parent type, insert k
successive event bits, one for each child except the final DEFAULT
child. A child is positive at precisely its own event, and the last
child is all zero. The resulting bit codes are pairwise distinct.

This is the exact finite combinatorial core of the one-pass block
construction for both 1-splits and 2-splits. Terminal germs simply
become another child; a terminal singleton germ can be chosen as
the default (all-zero) child.

No diary geometry or full prefix transport is assumed or proved here.
-/

namespace ThreeUniformDiaries
namespace OnePass

/-- A block with k tests separates k+1 children; label k is
the unique all-zero default child. -/
def eventBit (k : Nat) (child : Fin (k + 1)) (event : Fin k) :
    Bool :=
  decide (child.val = event.val)

/-- The last child is not positive at any event. -/
theorem default_all_zero (k : Nat) (event : Fin k) :
    eventBit k ⟨k, by omega⟩ event = false := by
  simp [eventBit]
  omega

/-- Each non-default child is positive at its own event. -/
theorem named_child_positive
    (k : Nat) (event : Fin k) :
    eventBit k ⟨event.val, by omega⟩ event = true := by
  simp [eventBit]

/-- Positive events do not overlap: another child has a negative bit. -/
theorem other_child_negative
    (k : Nat) (child : Fin (k + 1)) (event : Fin k)
    (hne : child.val ≠ event.val) :
    eventBit k child event = false := by
  simp [eventBit, hne]

/-- No two distinct refinement children have the same vector
of k event bits. -/
theorem event_code_injective
    (k : Nat) :
    Function.Injective (fun child : Fin (k + 1) =>
      fun event : Fin k => eventBit k child event) := by
  intro x y heq
  apply Fin.ext
  by_cases hx : x.val < k
  · let event : Fin k := ⟨x.val, hx⟩
    have hbits := congrFun heq event
    have hyx : y.val = x.val := by
      simpa [eventBit, event] using hbits
    omega
  · have hxlast : x.val = k := by
      have hxb := x.isLt
      omega
    by_cases hy : y.val < k
    · let event : Fin k := ⟨y.val, hy⟩
      have hbits := congrFun heq event
      have hne : x.val ≠ event.val := by
        simp only [event]
        omega
      have hbad : False := by
        simpa [eventBit, event, hne] using hbits
      exact False.elim hbad
    · have hylast : y.val = k := by
        have hyb := y.isLt
        omega
      omega

/-- Equality of refinement children is equivalent to equality
of their complete bit patterns. -/
theorem event_code_eq_iff (k : Nat) (x y : Fin (k + 1)) :
    (∀ event : Fin k, eventBit k x event = eventBit k y event) ↔
      x = y := by
  constructor
  · intro h
    apply event_code_injective k
    funext event
    exact h event
  · intro h
    subst y
    intro event
    rfl

end OnePass
end ThreeUniformDiaries
