import ThreeUniformDiaries.RootGluedScalarStrong

/-!
# A synchronized strong vector picture as a typed scalar glued carrier

The three coordinate strong subtrees all share one selected level map f.
Their union must remain typed, so that the newly added root has exactly
the E0, E1 and E2 child cones and no accidental component overlap.

This constructs the literal underlying scalar carrier from the three
genuine InfiniteStrongPicture witnesses. Root-child and successor
strongness in the ambient glued tree are separate theorems.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Ancestor order cannot cross from one type-tree coordinate to
another. -/
theorem sort_eq_of_le {x y : CoordNode} (hxy : x ≤ y) :
    sort x = sort y := by
  have htr := hxy.2
  cases x with
  | aux n a =>
      cases y with
      | aux m b => rfl
      | one m b => cases htr
      | enum m b => cases htr
  | one n a =>
      cases y with
      | aux m b => cases htr
      | one m b => rfl
      | enum m b => cases htr
  | enum n a =>
      cases y with
      | aux m b => cases htr
      | one m b => cases htr
      | enum m b => rfl

/-- Truncating a type node never changes its coordinate sort. -/
theorem sort_truncate (x : CoordNode) (k : Nat) :
    sort (truncate x k) = sort x := by
  cases x <;> rfl

/-- The abstract coordinate meet stays in the left coordinate sort. -/
theorem sort_meet (x y : CoordNode) :
    sort (CoordNode.meet x y) = sort x := by
  exact sort_truncate x (meetLevel x y)

/-- Convert an honest synchronized triple of infinite strong type
trees into its typed three-coordinate carrier. -/
def typedVectorOfStrong
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    TypedVectorSubset where
  carrier := ![S₀, S₁, S₂]
  correctlyTyped := by
    intro i x hx
    fin_cases i
    · change x ∈ S₀ at hx
      exact (sort_eq_of_le (h₀.root_le x hx)).symm
    · change x ∈ S₁ at hx
      exact (sort_eq_of_le (h₁.root_le x hx)).symm
    · change x ∈ S₂ at hx
      exact (sort_eq_of_le (h₂.root_le x hx)).symm

@[simp] theorem typedVectorOfStrong_enum
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    (typedVectorOfStrong h₀ h₁ h₂).carrier 0 = S₀ := rfl

@[simp] theorem typedVectorOfStrong_one
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    (typedVectorOfStrong h₀ h₁ h₂).carrier 1 = S₁ := rfl

@[simp] theorem typedVectorOfStrong_aux
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    (typedVectorOfStrong h₀ h₁ h₂).carrier 2 = S₂ := rfl

end CoordNode
end ThreeUniformDiaries
