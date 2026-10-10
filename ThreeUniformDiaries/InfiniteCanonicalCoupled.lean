import ThreeUniformDiaries.InfiniteCanonicalAux

/-!
# The actual infinite canonical maps in all three coordinates

The abstract manuscript maps on an infinite strong vector subtree
are constructed, not postulated as fields of CanonicalMap. Their
recursive dependence is triangular:

  E2 auxiliary bits -> E1 singleton parameters -> E0 enumerations.

The geometric InfiniteStrongPicture supplies a unique node in every
chosen ambient immediate child cone. All three total maps on arbitrary
natural source levels return nodes with membership certificates
in the corresponding selected strong coordinate tree.

Exact restriction and type preservation will be proved separately,
and infinite strong vector-tree representations remain an interface.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The unique next selected one node for any retained node and
boundary parameter, across an arbitrary finite ambient level gap. -/
theorem infiniteStrongPicture_one_lift
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (i : Nat) (a : OneNode (f i))
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
  obtain ⟨z, ⟨hz, hzlevel, htz⟩, hunique⟩ :=
    hS.next_child i p ha rfl t hcover
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

/-- Canonical one next-step choice in the infinite strong picture. -/
noncomputable def infiniteStrongPicture_oneStep
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (i : Nat) (a : OneNode (f i))
    (ha : CoordNode.one (f i) a ∈ S)
    (c : AuxNode (f i)) :
    OneNode (f (i + 1)) :=
  Classical.choose (infiniteStrongPicture_one_lift hS i a ha c)

theorem infiniteStrongPicture_oneStep_spec
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (i : Nat) (a : OneNode (f i))
    (ha : CoordNode.one (f i) a ∈ S)
    (c : AuxNode (f i)) :
    CoordNode.one (f (i + 1))
      (infiniteStrongPicture_oneStep hS i a ha c) ∈ S ∧
    CoordNode.one (f i + 1) (a.succ c) ≤
      CoordNode.one (f (i + 1))
        (infiniteStrongPicture_oneStep hS i a ha c) :=
  (Classical.choose_spec
    (infiniteStrongPicture_one_lift hS i a ha c)).1


/-- The unique next selected enum node for any retained node and
boundary parameter, across an arbitrary finite ambient level gap. -/
theorem infiniteStrongPicture_enum_lift
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (i : Nat) (a : EnumNode (f i))
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
  obtain ⟨z, ⟨hz, hzlevel, htz⟩, hunique⟩ :=
    hS.next_child i p ha rfl t hcover
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

/-- Canonical enum next-step choice in the infinite strong picture. -/
noncomputable def infiniteStrongPicture_enumStep
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (i : Nat) (a : EnumNode (f i))
    (ha : CoordNode.enum (f i) a ∈ S)
    (d : OneNode (f i)) :
    EnumNode (f (i + 1)) :=
  Classical.choose (infiniteStrongPicture_enum_lift hS i a ha d)

theorem infiniteStrongPicture_enumStep_spec
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (i : Nat) (a : EnumNode (f i))
    (ha : CoordNode.enum (f i) a ∈ S)
    (d : OneNode (f i)) :
    CoordNode.enum (f (i + 1))
      (infiniteStrongPicture_enumStep hS i a ha d) ∈ S ∧
    CoordNode.enum (f i + 1) (a.succ d) ≤
      CoordNode.enum (f (i + 1))
        (infiniteStrongPicture_enumStep hS i a ha d) :=
  (Classical.choose_spec
    (infiniteStrongPicture_enum_lift hS i a ha d)).1


/-- A genuine all-level singleton canonical map with its lower
auxiliary coordinate map as the successor parameter. -/
noncomputable def infiniteOneCanonicalMap
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    (i : Nat) → OneNode i →
      {b : OneNode (f i) // CoordNode.one (f i) b ∈ S₁}
  | 0, _ => ⟨r₁, h₁.root_mem⟩
  | i + 1, a => by
      let prev := infiniteOneCanonicalMap h₁ h₂ i (a.truncate i)
      let param := infiniteAuxCanonicalMap h₂ i (a.boundaryAux i)
      let b := infiniteStrongPicture_oneStep h₁ i
        prev.val prev.property param.val
      have hb :=
        (infiniteStrongPicture_oneStep_spec h₁ i
          prev.val prev.property param.val).1
      exact ⟨b, hb⟩

/-- A genuine all-level enumeration canonical map. Every new
enumeration-type parameter is supplied by the constructed E1 map. -/
noncomputable def infiniteEnumCanonicalMap
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂)) :
    (i : Nat) → EnumNode i →
      {b : EnumNode (f i) // CoordNode.enum (f i) b ∈ S₀}
  | 0, _ => ⟨r₀, h₀.root_mem⟩
  | i + 1, a => by
      let prev := infiniteEnumCanonicalMap h₀ h₁ h₂ i (a.truncate i)
      let param := infiniteOneCanonicalMap h₁ h₂ i (a.boundaryOne i)
      let b := infiniteStrongPicture_enumStep h₀ i
        prev.val prev.property param.val
      have hb :=
        (infiniteStrongPicture_enumStep_spec h₀ i
          prev.val prev.property param.val).1
      exact ⟨b, hb⟩

@[simp] theorem infiniteOneCanonicalMap_root
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (a : OneNode 0) :
    (infiniteOneCanonicalMap h₁ h₂ 0 a).val = r₁ := rfl

@[simp] theorem infiniteEnumCanonicalMap_root
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (a : EnumNode 0) :
    (infiniteEnumCanonicalMap h₀ h₁ h₂ 0 a).val = r₀ := rfl

end CoordNode
end ThreeUniformDiaries
