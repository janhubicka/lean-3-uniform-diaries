import ThreeUniformDiaries.RootGluedStrongCarrier

/-!
# The added root has exactly one chosen node in each scalar child cone

The three scalar root children are the unique zero-level E0, E1, E2
types. A synchronized strong vector picture provides precisely one
root in each of those cones, on the common first selected level
f(0)+1. This checks the most delicate new branch introduced by
root-gluing; above the root the successor law is coordinatewise.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Zero-level type nodes lie below all nodes of the same sort. -/
theorem zero_le_of_sort (t r : CoordNode)
    (ht : level t = 0) (hsort : sort t = sort r) :
    t ≤ r := by
  cases t with
  | aux n a =>
      have hn : n = 0 := ht
      subst n
      cases r with
      | aux m b => exact aux_zero_le a b
      | one m b => simp [sort] at hsort
      | enum m b => simp [sort] at hsort
  | one n a =>
      have hn : n = 0 := ht
      subst n
      cases r with
      | aux m b => simp [sort] at hsort
      | one m b => exact one_zero_le a b
      | enum m b => simp [sort] at hsort
  | enum n a =>
      have hn : n = 0 := ht
      subst n
      cases r with
      | aux m b => simp [sort] at hsort
      | one m b => simp [sort] at hsort
      | enum m b => exact enum_zero_le a b

/-- A typed scalar carrier with a chosen first-level root in a sort
and no other first-level node of that sort has a unique representative
of every zero-level child cone of that sort. -/
theorem glued_root_cone_unique
    (V : TypedVectorSubset) (m : Nat) (r : CoordNode)
    (hrMem : r ∈ V.carrier (sort r))
    (hrLevel : level r = m)
    (hrootLe : ∀ y ∈ V.carrier (sort r), r ≤ y)
    (t : CoordNode) (ht : level t = 0)
    (htSort : sort t = sort r) :
    ∃! z : GluedNode,
      z ∈ V.glue ∧ gluedLevel z = m + 1 ∧
        gluedLE (some t) z := by
  refine ⟨some r, ⟨(V.some_mem_iff r).mpr hrMem,
    by simpa only [gluedLevel] using congrArg Nat.succ hrLevel,
    zero_le_of_sort t r ht htSort⟩, ?_⟩
  intro z hz
  cases z with
  | none =>
      have hfalse : (0 : Nat) = m + 1 := hz.2.1
      omega
  | some y =>
      have hty : t ≤ y := hz.2.2
      have hysort : sort y = sort r :=
        (sort_eq_of_le hty).symm.trans htSort
      have hyMem : y ∈ V.carrier (sort r) := by
        have hy : y ∈ V.union :=
          (V.some_mem_iff y).mp hz.1
        change y ∈ V.carrier (sort y) at hy
        rw [hysort] at hy
        exact hy
      have hyLevel : level y = m := by
        change level y + 1 = m + 1 at hz
        omega
      have hry : r ≤ y := hrootLe y hyMem
      have hEq : y = r :=
        (eq_of_le_of_level_eq hry
          (hrLevel.trans hyLevel.symm)).symm
      exact congrArg Option.some hEq

/-- Every immediate successor cone of the newly glued root is
represented uniquely on the first common selected scalar level. -/
theorem gluedVectorStrongCarrier_root_child
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    ∀ t : GluedNode, gluedChild none t →
      ∃! z : GluedNode,
        z ∈ gluedVectorStrongCarrier h₀ h₁ h₂ ∧
          gluedLevel z = f 0 + 1 ∧ gluedLE t z := by
  intro t ht
  cases t with
  | none => exact False.elim ht
  | some t =>
      cases t with
      | aux n a =>
          have hn : n = 0 := ht
          subst n
          exact glued_root_cone_unique
            (typedVectorOfStrong h₀ h₁ h₂) (f 0)
            (.aux (f 0) r₂) h₂.root_mem rfl
            (fun y hy => h₂.root_le y hy)
            (.aux 0 a) rfl rfl
      | one n a =>
          have hn : n = 0 := ht
          subst n
          exact glued_root_cone_unique
            (typedVectorOfStrong h₀ h₁ h₂) (f 0)
            (.one (f 0) r₁) h₁.root_mem rfl
            (fun y hy => h₁.root_le y hy)
            (.one 0 a) rfl rfl
      | enum n a =>
          have hn : n = 0 := ht
          subst n
          exact glued_root_cone_unique
            (typedVectorOfStrong h₀ h₁ h₂) (f 0)
            (.enum (f 0) r₀) h₀.root_mem rfl
            (fun y hy => h₀.root_le y hy)
            (.enum 0 a) rfl rfl

end CoordNode
end ThreeUniformDiaries
