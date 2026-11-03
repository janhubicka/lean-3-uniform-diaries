import ThreeUniformDiaries.RootGluedStrongRootCones

/-!
# Scalar successor cones away from the new root

Inside any one of the three coordinate cones, the scalar glued
tree's order and immediate successor relation are literally the
original coordinate-tree order and immediate successor relation.

A genuine strong coordinate picture therefore supplies exactly one
selected scalar successor in every scalar ambient child cone above
its retained nodes. Together with the independent added-root theorem
this proves the FULL forward strong-subtree direction of root-gluing.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Lift the selected-cone law of one genuine coordinate picture
to the scalar glued tree, provided that the typed scalar carrier's
slice in that coordinate is literally the picture S. -/
theorem glued_coordinate_next_child
    (V : TypedVectorSubset)
    {S : Set CoordNode} {f : Nat → Nat} {root : CoordNode}
    (hS : InfiniteStrongPicture S f root)
    (hSlice : ∀ y : CoordNode,
      y ∈ S ↔ y ∈ V.carrier (sort root))
    (i : Nat) (p : CoordNode)
    (hp : p ∈ S) (hpLevel : level p = f i)
    (t : CoordNode) (hpt : p ⋖ t) :
    ∃! z : GluedNode,
      z ∈ V.glue ∧ gluedLevel z = f (i + 1) + 1 ∧
        gluedLE (some t) z := by
  obtain ⟨z, ⟨hzS, hzLevel, htz⟩, hunique⟩ :=
    hS.next_child i p hp hpLevel t hpt
  have hzr : sort z = sort root :=
    (sort_eq_of_le (hS.root_le z hzS)).symm
  have hzCarrier : z ∈ V.carrier (sort z) := by
    rw [hzr]
    exact (hSlice z).mp hzS
  have hzMem : some z ∈ V.glue :=
    (V.some_mem_iff z).mpr hzCarrier
  refine ⟨some z, ⟨hzMem,
    by simpa only [gluedLevel] using congrArg Nat.succ hzLevel,
    htz⟩, ?_⟩
  intro w hw
  cases w with
  | none =>
      have hf : (0 : Nat) = f (i + 1) + 1 := hw.2.1
      omega
  | some w =>
      have htw : t ≤ w := hw.2.2
      have hrootp : sort root = sort p :=
        sort_eq_of_le (hS.root_le p hp)
      have hptsort : sort p = sort t := sort_eq_of_le hpt.le
      have htsort : sort t = sort w := sort_eq_of_le htw
      have hwr : sort w = sort root :=
        htsort.symm.trans (hptsort.symm.trans hrootp.symm)
      have hwCarrier : w ∈ V.carrier (sort w) :=
        (V.some_mem_iff w).mp hw.1
      have hwS : w ∈ S := by
        rw [hwr] at hwCarrier
        exact (hSlice w).mpr hwCarrier
      have hwLevel : level w = f (i + 1) := by
        have hl : level w + 1 = f (i + 1) + 1 := hw.2.1
        omega
      have hEq : w = z :=
        hunique w ⟨hwS, hwLevel, htw⟩
      exact congrArg Option.some hEq

/-- Every retained scalar node away from the new root has exactly
one next selected scalar representative in each of its immediate
ambient successor cones. -/
theorem gluedVectorStrongCarrier_next_child
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    ∀ (i : Nat) (p : GluedNode),
      p ∈ gluedVectorStrongCarrier h₀ h₁ h₂ →
      gluedLevel p = f i + 1 →
      ∀ t : GluedNode, gluedChild p t →
      ∃! z : GluedNode,
        z ∈ gluedVectorStrongCarrier h₀ h₁ h₂ ∧
          gluedLevel z = f (i + 1) + 1 ∧ gluedLE t z := by
  intro i p hp hpLevel t hpt
  cases p with
  | none =>
      have hl : (0 : Nat) = f i + 1 := hpLevel
      omega
  | some p =>
      cases t with
      | none => exact False.elim hpt
      | some t =>
          cases p with
          | aux n a =>
              have hpa : CoordNode.aux n a ∈ S₂ :=
                (gluedVectorStrongCarrier_aux_iff h₀ h₁ h₂ n a).mp hp
              have hpl : level (CoordNode.aux n a) = f i := by
                have h : n + 1 = f i + 1 := hpLevel
                simpa only [level] using Nat.add_right_cancel h
              exact glued_coordinate_next_child
                (typedVectorOfStrong h₀ h₁ h₂) h₂
                (fun y => Iff.rfl) i (.aux n a) hpa hpl t hpt
          | one n a =>
              have hpa : CoordNode.one n a ∈ S₁ :=
                (gluedVectorStrongCarrier_one_iff h₀ h₁ h₂ n a).mp hp
              have hpl : level (CoordNode.one n a) = f i := by
                have h : n + 1 = f i + 1 := hpLevel
                simpa only [level] using Nat.add_right_cancel h
              exact glued_coordinate_next_child
                (typedVectorOfStrong h₀ h₁ h₂) h₁
                (fun y => Iff.rfl) i (.one n a) hpa hpl t hpt
          | enum n a =>
              have hpa : CoordNode.enum n a ∈ S₀ :=
                (gluedVectorStrongCarrier_enum_iff h₀ h₁ h₂ n a).mp hp
              have hpl : level (CoordNode.enum n a) = f i := by
                have h : n + 1 = f i + 1 := hpLevel
                simpa only [level] using Nat.add_right_cancel h
              exact glued_coordinate_next_child
                (typedVectorOfStrong h₀ h₁ h₂) h₀
                (fun y => Iff.rfl) i (.enum n a) hpa hpl t hpt

/-- The complete *forward* strong-subtree correspondence for
root-gluing the three synchronized genuine coordinate pictures. -/
theorem gluedVectorStrongCarrier_strong
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    RootedGluedInfiniteStrong
      (gluedVectorStrongCarrier h₀ h₁ h₂) f := by
  exact ⟨gluedVectorStrongCarrier_root_mem h₀ h₁ h₂,
    gluedVectorStrongCarrier_meet_closed h₀ h₁ h₂,
    gluedVectorStrongCarrier_selected_levels h₀ h₁ h₂,
    gluedVectorStrongCarrier_all_levels h₀ h₁ h₂,
    gluedVectorStrongCarrier_root_child h₀ h₁ h₂,
    gluedVectorStrongCarrier_next_child h₀ h₁ h₂⟩

end CoordNode
end ThreeUniformDiaries
