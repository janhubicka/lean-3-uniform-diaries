import ThreeUniformDiaries.AuxTypes

/-!
# Adding one level to singleton and auxiliary type agreement

The two steps in the proof of `lem:auxtypeemb` are literal recurrences
of the type-agreement relations. One-type agreement through `l + 1`
is one-type agreement through `l` plus the new pairs `(i,l)`;
auxiliary two-type agreement through `l + 1` is agreement through
`l` plus the new bit at `l`.

These statements identify the precise first-difference witnesses used in
the proof, but do not yet show that a canonical strong-subtree embedding
preserves the *exact* first-difference level.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Extending an aux-type comparison by one vertex tests exactly one new
edge bit. -/
theorem sameAuxTypeBelow_succ_iff
    (H : Ordered3Graph Nat) (l u₀ u₁ v₀ v₁ : Nat) :
    H.SameAuxTypeBelow (l + 1) u₀ u₁ v₀ v₁ ↔
      H.SameAuxTypeBelow l u₀ u₁ v₀ v₁ ∧
      (H.edge l u₀ u₁ ↔ H.edge l v₀ v₁) := by
  constructor
  · intro h
    constructor
    · intro a ha
      exact h (by omega)
    · exact h (by omega)
  · rintro ⟨hbefore, hat⟩ a ha
    by_cases hal : a < l
    · exact hbefore hal
    · have heq : a = l := by omega
      subst a
      exact hat

/-- Extending a singleton-type comparison by one vertex tests the new
pairs whose second ordinary coordinate is `l`. -/
theorem sameOneTypeBelow_succ_iff
    (H : Ordered3Graph Nat) (l u v : Nat) :
    H.SameOneTypeBelow (l + 1) u v ↔
      H.SameOneTypeBelow l u v ∧
      ∀ a : Nat, a < l →
        (H.edge a l u ↔ H.edge a l v) := by
  constructor
  · intro h
    constructor
    · intro a b hab hb
      exact h hab (by omega)
    · intro a ha
      exact h ha (by omega)
  · rintro ⟨hbefore, hnew⟩ a b hab hb
    by_cases hbl : b < l
    · exact hbefore hab hbl
    · have heq : b = l := by omega
      subst b
      exact hnew a hab

end Ordered3Graph
end ThreeUniformDiaries
