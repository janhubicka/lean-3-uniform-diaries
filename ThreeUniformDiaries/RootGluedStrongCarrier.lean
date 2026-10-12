import ThreeUniformDiaries.RootGluedTypedStrongVector

/-!
# Concrete scalar root-gluing: meet closure and selected levels

Three genuine synchronized strong E0/E1/E2 pictures, glued under one
new root, yield a scalar subset whose ambient meets are retained.
The set has the new scalar root and occupies exactly the selected
scalar levels 0,f(0)+1,f(1)+1,...

This verifies the non-branching portion of intrinsic scalar strongness.
Root cone and subsequent selected-cone uniqueness are isolated in
the next module, rather than assumed.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The actual scalar subset produced by gluing synchronized genuine
strong coordinate pictures with common level map f. -/
def gluedVectorStrongCarrier
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    Set GluedNode :=
  (typedVectorOfStrong h₀ h₁ h₂).glue

@[simp] theorem gluedVectorStrongCarrier_root_mem
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    none ∈ gluedVectorStrongCarrier h₀ h₁ h₂ :=
  (typedVectorOfStrong h₀ h₁ h₂).root_mem

@[simp] theorem gluedVectorStrongCarrier_enum_iff
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (n : Nat) (a : EnumNode n) :
    some (CoordNode.enum n a) ∈
      gluedVectorStrongCarrier h₀ h₁ h₂ ↔
    CoordNode.enum n a ∈ S₀ := by
  exact (typedVectorOfStrong h₀ h₁ h₂).some_mem_iff _

@[simp] theorem gluedVectorStrongCarrier_one_iff
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (n : Nat) (a : OneNode n) :
    some (CoordNode.one n a) ∈
      gluedVectorStrongCarrier h₀ h₁ h₂ ↔
    CoordNode.one n a ∈ S₁ := by
  exact (typedVectorOfStrong h₀ h₁ h₂).some_mem_iff _

@[simp] theorem gluedVectorStrongCarrier_aux_iff
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (n : Nat) (a : AuxNode n) :
    some (CoordNode.aux n a) ∈
      gluedVectorStrongCarrier h₀ h₁ h₂ ↔
    CoordNode.aux n a ∈ S₂ := by
  exact (typedVectorOfStrong h₀ h₁ h₂).some_mem_iff _

/-- The glued carrier occupies exactly root level 0 and the common
shifted selected levels of the three coordinates. -/
theorem gluedVectorStrongCarrier_selected_levels
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    ∀ x ∈ gluedVectorStrongCarrier h₀ h₁ h₂,
      x = none ∨ ∃ i : Nat, gluedLevel x = f i + 1 := by
  intro x hx
  cases x with
  | none => exact Or.inl rfl
  | some x =>
      right
      cases x with
      | aux n a =>
          have hxa : CoordNode.aux n a ∈ S₂ :=
            (gluedVectorStrongCarrier_aux_iff h₀ h₁ h₂ n a).mp hx
          obtain ⟨i, hi⟩ := h₂.selected_levels _ hxa
          exact ⟨i, by simpa only [gluedLevel] using congrArg Nat.succ hi⟩
      | one n a =>
          have hxa : CoordNode.one n a ∈ S₁ :=
            (gluedVectorStrongCarrier_one_iff h₀ h₁ h₂ n a).mp hx
          obtain ⟨i, hi⟩ := h₁.selected_levels _ hxa
          exact ⟨i, by simpa only [gluedLevel] using congrArg Nat.succ hi⟩
      | enum n a =>
          have hxa : CoordNode.enum n a ∈ S₀ :=
            (gluedVectorStrongCarrier_enum_iff h₀ h₁ h₂ n a).mp hx
          obtain ⟨i, hi⟩ := h₀.selected_levels _ hxa
          exact ⟨i, by simpa only [gluedLevel] using congrArg Nat.succ hi⟩

/-- Every positive selected scalar level has a node; any one of the
coordinate trees supplies it. -/
theorem gluedVectorStrongCarrier_all_levels
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    ∀ i : Nat, ∃ x ∈ gluedVectorStrongCarrier h₀ h₁ h₂,
      gluedLevel x = f i + 1 := by
  intro i
  obtain ⟨x, hx, hlev⟩ := h₂.all_levels i
  cases x with
  | aux n a =>
      exact ⟨some (.aux n a),
        (gluedVectorStrongCarrier_aux_iff h₀ h₁ h₂ n a).mpr hx,
        by simpa only [gluedLevel] using congrArg Nat.succ hlev⟩
  | one n a =>
      have hs := sort_eq_of_le (h₂.root_le (.one n a) hx)
      simp [sort] at hs
  | enum n a =>
      have hs := sort_eq_of_le (h₂.root_le (.enum n a) hx)
      simp [sort] at hs

/-- The ambient scalar meet of two glued retained nodes is retained. -/
theorem gluedVectorStrongCarrier_meet_closed
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    ∀ x ∈ gluedVectorStrongCarrier h₀ h₁ h₂,
      ∀ y ∈ gluedVectorStrongCarrier h₀ h₁ h₂,
      gluedMeet x y ∈ gluedVectorStrongCarrier h₀ h₁ h₂ := by
  intro x hx y hy
  cases x with
  | none =>
      change none ∈ gluedVectorStrongCarrier h₀ h₁ h₂
      exact gluedVectorStrongCarrier_root_mem h₀ h₁ h₂
  | some x =>
    cases y with
    | none =>
        change none ∈ gluedVectorStrongCarrier h₀ h₁ h₂
        exact gluedVectorStrongCarrier_root_mem h₀ h₁ h₂
    | some y =>
      cases x with
      | aux nx ax =>
        cases y with
        | aux ny ay =>
            change some (CoordNode.meet (.aux nx ax) (.aux ny ay)) ∈
              gluedVectorStrongCarrier h₀ h₁ h₂
            exact (gluedVectorStrongCarrier_aux_iff h₀ h₁ h₂ _ _).mpr
              (h₂.meet_closed
                ((gluedVectorStrongCarrier_aux_iff h₀ h₁ h₂ nx ax).mp hx)
                ((gluedVectorStrongCarrier_aux_iff h₀ h₁ h₂ ny ay).mp hy))
        | one ny ay =>
            exact gluedVectorStrongCarrier_root_mem h₀ h₁ h₂
        | enum ny ay =>
            exact gluedVectorStrongCarrier_root_mem h₀ h₁ h₂
      | one nx ax =>
        cases y with
        | aux ny ay =>
            exact gluedVectorStrongCarrier_root_mem h₀ h₁ h₂
        | one ny ay =>
            change some (CoordNode.meet (.one nx ax) (.one ny ay)) ∈
              gluedVectorStrongCarrier h₀ h₁ h₂
            exact (gluedVectorStrongCarrier_one_iff h₀ h₁ h₂ _ _).mpr
              (h₁.meet_closed
                ((gluedVectorStrongCarrier_one_iff h₀ h₁ h₂ nx ax).mp hx)
                ((gluedVectorStrongCarrier_one_iff h₀ h₁ h₂ ny ay).mp hy))
        | enum ny ay =>
            exact gluedVectorStrongCarrier_root_mem h₀ h₁ h₂
      | enum nx ax =>
        cases y with
        | aux ny ay =>
            exact gluedVectorStrongCarrier_root_mem h₀ h₁ h₂
        | one ny ay =>
            exact gluedVectorStrongCarrier_root_mem h₀ h₁ h₂
        | enum ny ay =>
            change some (CoordNode.meet (.enum nx ax) (.enum ny ay)) ∈
              gluedVectorStrongCarrier h₀ h₁ h₂
            exact (gluedVectorStrongCarrier_enum_iff h₀ h₁ h₂ _ _).mpr
              (h₀.meet_closed
                ((gluedVectorStrongCarrier_enum_iff h₀ h₁ h₂ nx ax).mp hx)
                ((gluedVectorStrongCarrier_enum_iff h₀ h₁ h₂ ny ay).mp hy))

end CoordNode
end ThreeUniformDiaries
