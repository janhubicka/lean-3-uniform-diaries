import ThreeUniformDiaries.RootGluedZeroLevelRigidity
import ThreeUniformDiaries.InfiniteCanonicalAux

/-!
# Actual synchronized ATR strong pictures as a typed root-glued carrier

A triple of genuine geometric InfiniteStrongPicture objects in E0,
E1, E2 with one common selected-level map determines a literal typed
vector subset: membership in each coordinate is the original strong
tree carrier, not a newly chosen copy.

The scalar root-gluing is precisely the union of these three carriers
plus the new root. Selected scalar levels are zero at the new root
and the old selected levels increased by one.

This is the concrete carrier part of the non-homogeneous Milliken
transfer. Intrinsic scalar strongness is checked separately.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Form the exact typed carrier of synchronized geometric strong
coordinate pictures. -/
def typedStrongVectorCarrier
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    TypedVectorSubset where
  carrier i := {x |
    (i = 0 ∧ x ∈ S₀) ∨
    (i = 1 ∧ x ∈ S₁) ∨
    (i = 2 ∧ x ∈ S₂)}
  correctlyTyped := by
    intro i x hx
    rcases hx with ⟨hi, hx⟩ | ⟨hi, hx⟩ | ⟨hi, hx⟩
    · subst i
      have hsort := sort_eq_of_le (h₀.root_le x hx)
      simpa only [sort] using hsort.symm
    · subst i
      have hsort := sort_eq_of_le (h₁.root_le x hx)
      simpa only [sort] using hsort.symm
    · subst i
      have hsort := sort_eq_of_le (h₂.root_le x hx)
      simpa only [sort] using hsort.symm

/-- The carrier in the glued forest contains exactly the three
actual strong coordinate sets, with no extra coordinate nodes. -/
theorem typedStrongVectorCarrier_union
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    (typedStrongVectorCarrier h₀ h₁ h₂).union =
      S₀ ∪ S₁ ∪ S₂ := by
  ext x
  constructor
  · intro hx
    change (sort x = 0 ∧ x ∈ S₀) ∨
      (sort x = 1 ∧ x ∈ S₁) ∨
      (sort x = 2 ∧ x ∈ S₂) at hx
    rcases hx with h | h | h
    · exact Or.inl h.2
    · exact Or.inr (Or.inl h.2)
    · exact Or.inr (Or.inr h.2)
  · intro hx
    rcases hx with hx | (hx | hx)
    · have hs : sort x = 0 :=
        (sort_eq_of_le (h₀.root_le x hx)).symm
      change (sort x = 0 ∧ x ∈ S₀) ∨
        (sort x = 1 ∧ x ∈ S₁) ∨
        (sort x = 2 ∧ x ∈ S₂)
      exact Or.inl ⟨hs, hx⟩
    · have hs : sort x = 1 :=
        (sort_eq_of_le (h₁.root_le x hx)).symm
      change (sort x = 0 ∧ x ∈ S₀) ∨
        (sort x = 1 ∧ x ∈ S₁) ∨
        (sort x = 2 ∧ x ∈ S₂)
      exact Or.inr (Or.inl ⟨hs, hx⟩)
    · have hs : sort x = 2 :=
        (sort_eq_of_le (h₂.root_le x hx)).symm
      change (sort x = 0 ∧ x ∈ S₀) ∨
        (sort x = 1 ∧ x ∈ S₁) ∨
        (sort x = 2 ∧ x ∈ S₂)
      exact Or.inr (Or.inr ⟨hs, hx⟩)

/-- All scalar nodes belong to the new root or one of the three
actual coordinate strong pictures, on shifted selected levels. -/
theorem typedStrongVectorCarrier_glued_levels
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (x : Option CoordNode)
    (hx : x ∈ (typedStrongVectorCarrier h₀ h₁ h₂).glue) :
    ∃ j : Nat,
      gluedLevel x = selectedGluedLevels f j := by
  have hlevels :
      ∀ i : Fin 3, ∀ y : CoordNode,
        y ∈ (typedStrongVectorCarrier h₀ h₁ h₂).carrier i →
          ∃ k : Nat, level y = f k := by
    intro i y hy
    rcases hy with ⟨_, hy⟩ | ⟨_, hy⟩ | ⟨_, hy⟩
    · exact h₀.selected_levels y hy
    · exact h₁.selected_levels y hy
    · exact h₂.selected_levels y hy
  rcases glued_selected_levels
      (typedStrongVectorCarrier h₀ h₁ h₂) f
      hlevels x hx with hroot | ⟨k, hk⟩
  · subst x
    exact ⟨0, rfl⟩
  · exact ⟨k + 1, hk⟩

end CoordNode
end ThreeUniformDiaries
