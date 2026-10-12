import ThreeUniformDiaries.InfiniteToFiniteStrongPrefix
import ThreeUniformDiaries.RootGluedSelectedStem

/-!
# Exact agreement of finite strong prefixes with selected source levels

For an actual infinite ATR strong picture, the nodes at or below
ambient height f(k) are precisely its first k+1 selected source
levels. Consequently its already-verified finite strong completion
and the scalar root-glued finite approximation use literally the
same finite carrier, even with arbitrarily large gaps in f.

This is the finite-height bridge needed to decode a general-tree
Milliken approximation as genuine finite E0/E1/E2 strong pictures.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The level-cut definition of a genuine finite strong prefix is
exactly the first k+1 selected source levels. -/
theorem infiniteStrongPicture_finitePrefix_eq_selected
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (hf : StrictMono f) (k : Nat) :
    infiniteStrongPicture_finitePrefix S f k =
      {x | x ∈ S ∧ ∃ j : Nat, j < k + 1 ∧ level x = f j} := by
  ext x
  constructor
  · rintro ⟨hx, hlevelBound⟩
    obtain ⟨j, hj⟩ := hS.selected_levels x hx
    have hjk : j ≤ k := by
      by_contra hnot
      have hkj : k < j := Nat.lt_of_not_ge hnot
      have hlt := hf hkj
      rw [hj] at hlevelBound
      omega
    exact ⟨hx, j, Nat.lt_succ_of_le hjk, hj⟩
  · rintro ⟨hx, j, hjk, hlevel⟩
    exact ⟨hx, by
      rw [hlevel]
      exact hf.monotone (Nat.le_of_lt_succ hjk)⟩

/-- The finite slice of any genuine coordinate strong picture is
literally the corresponding part of a typed selected vector prefix. -/
theorem typedVectorStrong_finiteSlice_eq
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) (k : Nat) :
    ((typedVectorOfStrong h₀ h₁ h₂).truncateSelected f (k + 1)).carrier 0 =
      infiniteStrongPicture_finitePrefix S₀ f k ∧
    ((typedVectorOfStrong h₀ h₁ h₂).truncateSelected f (k + 1)).carrier 1 =
      infiniteStrongPicture_finitePrefix S₁ f k ∧
    ((typedVectorOfStrong h₀ h₁ h₂).truncateSelected f (k + 1)).carrier 2 =
      infiniteStrongPicture_finitePrefix S₂ f k := by
  constructor
  · rw [infiniteStrongPicture_finitePrefix_eq_selected h₀ hf k]
    rfl
  constructor
  · rw [infiniteStrongPicture_finitePrefix_eq_selected h₁ hf k]
    rfl
  · rw [infiniteStrongPicture_finitePrefix_eq_selected h₂ hf k]
    rfl

end CoordNode
end ThreeUniformDiaries
