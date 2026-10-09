import ThreeUniformDiaries.FiniteStrongTypedAuxLift

/-!
# Typed canonical successor choices for the singleton and enumeration trees

The finite strong-picture property gives a unique next selected-level
node in every immediate ambient successor cone. This module refines
that generic uniqueness to the actual OneNode and EnumNode types, for
every retained node (not only prescribed Aemb candidates).

In the three-coordinate canonical-map recursion the singleton
successor parameter is an already mapped AuxNode; the enumeration
successor parameter is an already mapped OneNode.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The canonical one successor at the next selected height,
with any permitted parameter on the current selected height. -/
theorem finiteStrongPicture_one_lift
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (i : Nat) (hi : i < k)
    (a : OneNode (f i))
    (ha : CoordNode.one (f i) a ∈ S)
    (c : AuxNode (f i)) :
    ∃! b : OneNode (f (i + 1)),
      CoordNode.one (f (i + 1)) b ∈ S ∧
      CoordNode.one (f i + 1) (a.succ c) ≤
        CoordNode.one (f (i + 1)) b := by
  let p := CoordNode.one (f i) a
  let t := CoordNode.one (f i + 1) (a.succ c)
  have hpt : p ≤ t := by
    refine ⟨by dsimp [p, t, level]; omega, ?_⟩
    simp [p, t, level, truncate]
  have hcover : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
    change level t = level p + 1
    rfl
  rcases hS with ⟨_, _, _, _, _, _, hchildren⟩
  obtain ⟨z, ⟨hz, hzlevel, htz⟩, hunique⟩ :=
    hchildren i hi p ha rfl t hcover
  cases z with
  | aux j b =>
      have hcontra := htz.2
      simp [t, level, truncate] at hcontra
  | one j b =>
      have hj : j = f (i + 1) := hzlevel
      subst j
      refine ⟨b, ⟨hz, htz⟩, ?_⟩
      intro c ⟨hc, htc⟩
      have heq := hunique (CoordNode.one (f (i + 1)) c)
        ⟨hc, rfl, htc⟩
      cases heq
      rfl
  | enum j b =>
      have hcontra := htz.2
      simp [t, level, truncate] at hcontra

/-- A canonical typed one successor choice, to be used by the
coupled finite three-coordinate map recursion. -/
noncomputable def finiteStrongPicture_oneStep
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat} {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (i : Nat) (hi : i < k)
    (a : OneNode (f i))
    (ha : CoordNode.one (f i) a ∈ S)
    (c : AuxNode (f i)) :
    OneNode (f (i + 1)) :=
  Classical.choose (finiteStrongPicture_one_lift hS i hi a ha c)

theorem finiteStrongPicture_oneStep_spec
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat} {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (i : Nat) (hi : i < k)
    (a : OneNode (f i))
    (ha : CoordNode.one (f i) a ∈ S)
    (c : AuxNode (f i)) :
    CoordNode.one (f (i + 1))
        (finiteStrongPicture_oneStep hS i hi a ha c) ∈ S ∧
      CoordNode.one (f i + 1) (a.succ c) ≤
        CoordNode.one (f (i + 1))
          (finiteStrongPicture_oneStep hS i hi a ha c) :=
  (Classical.choose_spec (finiteStrongPicture_one_lift hS i hi a ha c)).1


/-- The canonical enum successor at the next selected height,
with any permitted parameter on the current selected height. -/
theorem finiteStrongPicture_enum_lift
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (i : Nat) (hi : i < k)
    (a : EnumNode (f i))
    (ha : CoordNode.enum (f i) a ∈ S)
    (d : OneNode (f i)) :
    ∃! b : EnumNode (f (i + 1)),
      CoordNode.enum (f (i + 1)) b ∈ S ∧
      CoordNode.enum (f i + 1) (a.succ d) ≤
        CoordNode.enum (f (i + 1)) b := by
  let p := CoordNode.enum (f i) a
  let t := CoordNode.enum (f i + 1) (a.succ d)
  have hpt : p ≤ t := by
    refine ⟨by dsimp [p, t, level]; omega, ?_⟩
    simp [p, t, level, truncate]
  have hcover : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
    change level t = level p + 1
    rfl
  rcases hS with ⟨_, _, _, _, _, _, hchildren⟩
  obtain ⟨z, ⟨hz, hzlevel, htz⟩, hunique⟩ :=
    hchildren i hi p ha rfl t hcover
  cases z with
  | aux j b =>
      have hcontra := htz.2
      simp [t, level, truncate] at hcontra
  | one j b =>
      have hcontra := htz.2
      simp [t, level, truncate] at hcontra
  | enum j b =>
      have hj : j = f (i + 1) := hzlevel
      subst j
      refine ⟨b, ⟨hz, htz⟩, ?_⟩
      intro c ⟨hc, htc⟩
      have heq := hunique (CoordNode.enum (f (i + 1)) c)
        ⟨hc, rfl, htc⟩
      cases heq
      rfl

/-- A canonical typed enum successor choice, to be used by the
coupled finite three-coordinate map recursion. -/
noncomputable def finiteStrongPicture_enumStep
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat} {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (i : Nat) (hi : i < k)
    (a : EnumNode (f i))
    (ha : CoordNode.enum (f i) a ∈ S)
    (d : OneNode (f i)) :
    EnumNode (f (i + 1)) :=
  Classical.choose (finiteStrongPicture_enum_lift hS i hi a ha d)

theorem finiteStrongPicture_enumStep_spec
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat} {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (i : Nat) (hi : i < k)
    (a : EnumNode (f i))
    (ha : CoordNode.enum (f i) a ∈ S)
    (d : OneNode (f i)) :
    CoordNode.enum (f (i + 1))
        (finiteStrongPicture_enumStep hS i hi a ha d) ∈ S ∧
      CoordNode.enum (f i + 1) (a.succ d) ≤
        CoordNode.enum (f (i + 1))
          (finiteStrongPicture_enumStep hS i hi a ha d) :=
  (Classical.choose_spec (finiteStrongPicture_enum_lift hS i hi a ha d)).1

end CoordNode
end ThreeUniformDiaries
