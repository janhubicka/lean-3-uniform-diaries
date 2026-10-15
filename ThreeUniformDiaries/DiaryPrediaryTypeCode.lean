import Mathlib

/-!
# Prefix-type factorisation after an inserted split

In the pre-diary completion algorithm the old cut moves as
vertices are inserted. Fixed-cut finiteness is useful only
if each new bit depends on already existing original type
information. This module isolates and verifies that statement
for abstract Boolean type codes.

It does not show that the manuscript's concrete V/E/S
insertion has the required factorisation or progress.
-/

namespace ThreeUniformDiaries
namespace PrediaryCode

variable {α : Type*}

/-- Agreement of all bits strictly below an old level k. -/
def PrefixEq (ty : α → Nat → Bool) (k : Nat) (a b : α) : Prop :=
  ∀ j, j < k → ty a j = ty b j

/-- Insert a bit at level n and shift every old bit >= n. -/
def insertBit (ty : α → Nat → Bool) (n : Nat)
    (newBit : α → Bool) (a : α) (j : Nat) : Bool :=
  if j < n then ty a j
  else if j = n then newBit a
  else ty a (j - 1)

/-- Every old bit remains accessible at its shifted position. -/
theorem insertBit_old
    (ty : α → Nat → Bool) (n : Nat)
    (newBit : α → Bool) (a : α) (j : Nat) :
    insertBit ty n newBit a
      (if j < n then j else j + 1) = ty a j := by
  by_cases hj : j < n
  · simp [insertBit, hj]
  · have hn : ¬ j + 1 < n := by omega
    have heq : j + 1 ≠ n := by omega
    simp [insertBit, hj, hn, heq]

/-- A new bit which factors through the old type at n+1
cannot create distinctions at any fixed old cut k > n. -/
theorem prefixEq_insert_of_factor
    (ty : α → Nat → Bool) (n k : Nat)
    (newBit : α → Bool) (a b : α)
    (hnk : n < k)
    (hfactor : ∀ u v : α,
      PrefixEq ty (n + 1) u v → newBit u = newBit v)
    (h : PrefixEq ty k a b) :
    PrefixEq (insertBit ty n newBit) (k + 1) a b := by
  intro j hj
  by_cases hbelow : j < n
  · simp only [insertBit, if_pos hbelow]
    exact h j (by omega)
  · by_cases heq : j = n
    · subst j
      simp only [insertBit, if_neg (by omega : ¬ n < n),
        if_pos rfl]
      exact hfactor a b (by
        intro t ht
        exact h t (by omega))
    · have hsmall : j - 1 < k := by omega
      simp only [insertBit, if_neg hbelow, if_neg heq]
      exact h (j - 1) hsmall

/-- The reverse direction needs no factorisation hypothesis. -/
theorem prefixEq_old_of_insert
    (ty : α → Nat → Bool) (n k : Nat)
    (newBit : α → Bool) (a b : α)
    (hnk : n < k)
    (h : PrefixEq (insertBit ty n newBit) (k + 1) a b) :
    PrefixEq ty k a b := by
  intro j hj
  have hmap : (if j < n then j else j + 1) < k + 1 := by
    split_ifs <;> omega
  have heq := h (if j < n then j else j + 1) hmap
  simpa only [insertBit_old] using heq

/-- Exact fixed-old-cut type equivalence across the insertion. -/
theorem prefixEq_insert_iff_of_factor
    (ty : α → Nat → Bool) (n k : Nat)
    (newBit : α → Bool) (a b : α)
    (hnk : n < k)
    (hfactor : ∀ u v : α,
      PrefixEq ty (n + 1) u v → newBit u = newBit v) :
    PrefixEq (insertBit ty n newBit) (k + 1) a b ↔
      PrefixEq ty k a b := by
  constructor
  · exact prefixEq_old_of_insert ty n k newBit a b hnk
  · exact prefixEq_insert_of_factor ty n k newBit a b hnk hfactor

/-- Factorisation really is needed, even for two test points. -/
theorem arbitrary_new_bit_counterexample :
    ∃ (ty : Bool → Nat → Bool) (newBit : Bool → Bool),
      PrefixEq ty 1 false true ∧
      ¬ PrefixEq (insertBit ty 0 newBit) 2 false true := by
  refine ⟨(fun _ _ => false), id, ?_, ?_⟩
  · intro j hj
    rfl
  · intro h
    have hdiff := h 0 (by omega)
    simp [insertBit] at hdiff

end PrediaryCode
end ThreeUniformDiaries
