import ThreeUniformDiaries.DiaryReservedFiniteHorizonCompatibility

/-!
# Finite-choice compactness for monotone finite-horizon obligations

A descending family of nonempty subsets of a FINITE set has a
common element. Formally, if a finite set W of possible next-leaf
images contains some witness at every finite horizon, and a witness
at a later horizon is also a witness at every earlier horizon,
then ONE image in W works for all finite horizons.

This is the elementary compactness step available once a genuine
finite bound on next-leaf images has been proved. It is NOT valid
without finite W; the existing decreasing-Nat-sequences regression
proves that the unrestricted infinite-branching inference is false.

No hypothesis about countable diary unavoidability is used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Uniform finite branching turns arbitrarily long downward-closed
finite-horizon witnesses into one persistent choice of next image.

The conclusion is a single member of W satisfying all finite-horizon
predicates. It is NOT yet an infinite diary embedding: only one
finite choice has been stabilized. -/
theorem finite_choice_persistent_of_downward
    (W : Finset Nat) (P : Nat → Nat → Prop)
    (hDown : ∀ v n k : Nat, k ≤ n → P v n → P v k)
    (hCover : ∀ n : Nat, ∃ v : Nat, v ∈ W ∧ P v n) :
    ∃ v : Nat, v ∈ W ∧ ∀ n : Nat, P v n := by
  classical
  by_contra hNone
  have bad : ∀ v : Nat, v ∈ W → ∃ n : Nat, ¬ P v n := by
    intro v hv
    by_contra h
    push_neg at h
    exact hNone ⟨v,hv,h⟩
  let badN : Nat → Nat := fun v =>
    if hv : v ∈ W then Classical.choose (bad v hv) else 0
  have hBadN (v : Nat) (hv : v ∈ W) : ¬ P v (badN v) := by
    simp only [badN, dif_pos hv]
    exact Classical.choose_spec (bad v hv)
  let N := W.sup badN
  obtain ⟨v,hv,hP⟩ := hCover N
  have hBound : badN v ≤ N := by
    exact Finset.le_sup (f := badN) hv
  exact hBadN v hv (hDown v N (badN v) hBound hP)

end DiaryLeafPriority
end ThreeUniformDiaries
