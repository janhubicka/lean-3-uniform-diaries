import ThreeUniformDiaries.DiaryCofinalStageRestrictions

/-!
# A finite-stage inverse system need not have a coherent countable point

This is an elementary adversarial regression for a tempting invalid
countable-source argument: every finite level can be inhabited and
restriction can preserve admissibility, while NO compatible infinite
sequence exists if the levels have infinitely many possible maps.

Take strictly decreasing finite sequences in Nat. Every finite length
exists; restricting to a shorter prefix preserves the property.
But there is no infinite strictly decreasing sequence in Nat.

This is a logical/compactness counterexample, NOT a counterexample
inside the special class of full diaries. It identifies the missing
relative extension or fusion argument.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteStageNoncompactness

/-- Every finite level has a strictly decreasing sequence of Nats. -/
theorem finite_decreasing_exists (n : Nat) :
    ∃ f : Fin n → Nat, ∀ i j : Fin n, i < j → f j < f i := by
  refine ⟨fun i => n - i.val, ?_⟩
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hstrict : i.val < j.val := hij
  omega

/-- All shorter initial segments remain strictly decreasing. -/
theorem finite_decreasing_restrict
    {m n : Nat} (hmn : m ≤ n)
    (f : Fin n → Nat)
    (hf : ∀ i j : Fin n, i < j → f j < f i) :
    ∀ i j : Fin m, i < j →
      f ⟨j.val, by omega⟩ < f ⟨i.val, by omega⟩ := by
  intro i j hij
  exact hf ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij

/-- There is NO infinite Nat-valued strictly decreasing sequence,
despite the preceding nonempty, restriction-closed finite levels. -/
theorem no_infinite_decreasing :
    ¬ ∃ f : Nat → Nat, ∀ i j : Nat, i < j → f j < f i := by
  rintro ⟨f,hf⟩
  have hbound : ∀ n : Nat, f n + n ≤ f 0 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hstep := hf n (n + 1) (by omega)
      omega
  have h := hbound (f 0 + 1)
  omega

end FiniteStageNoncompactness
end DiaryLeafPriority
end ThreeUniformDiaries
