import ThreeUniformDiaries.FiniteStrongTypedAuxLift

/-!
# An actual infinite strong coordinate picture and its canonical auxiliary map

The manuscript's canonical-map lemma is stated for finite OR infinite
strong vector subtrees. Earlier Lean code constructed the exact finite
maps, while the all-level CanonicalMap structure assumed the restriction
and type-compatibility fields instead of deriving them.

Here an infinite strong picture S is axiomatized by precisely the
geometric strong-subtree data: a root, selected levels on one
strictly increasing map, and a UNIQUE next selected node in each
ambient immediate successor cone. The auxiliary map is then
constructed recursively for every natural source level, rather than
postulated with abstract compatibility fields.

The remaining steps are the coupled E1/E0 maps, their type identities,
and the association with a concrete infinite vector strong subtree.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Exact geometric strongness for an infinite coordinate picture. -/
structure InfiniteStrongPicture
    (S : Set CoordNode) (f : Nat → Nat)
    (root : CoordNode) : Prop where
  root_mem : root ∈ S
  root_le : ∀ x ∈ S, root ≤ x
  meet_closed : MeetClosed S
  selected_levels : ∀ x ∈ S, ∃ i : Nat, level x = f i
  all_levels : ∀ i : Nat, ∃ x ∈ S, level x = f i
  next_child :
    ∀ (i : Nat) (p : CoordNode),
      p ∈ S → level p = f i →
      ∀ t : CoordNode, p ⋖ t →
        ∃! z : CoordNode,
          z ∈ S ∧ level z = f (i + 1) ∧ t ≤ z

/-- Typed auxiliary successor in any selected ambient child cone of
an infinite strong picture; uniqueness comes from geometric strongness. -/
theorem infiniteStrongPicture_aux_lift
    {S : Set CoordNode} {f : Nat → Nat}
    {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (i : Nat) (a : AuxNode (f i))
    (ha : CoordNode.aux (f i) a ∈ S)
    (bit : Bool) :
    ∃! b : AuxNode (f (i + 1)),
      CoordNode.aux (f (i + 1)) b ∈ S ∧
      CoordNode.aux (f i + 1) (a.succ bit) ≤
        CoordNode.aux (f (i + 1)) b := by
  let p := CoordNode.aux (f i) a
  let t := CoordNode.aux (f i + 1) (a.succ bit)
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
      have hj : j = f (i + 1) := hzlevel
      subst j
      refine ⟨b, ⟨hz, htz⟩, ?_⟩
      intro c ⟨hc, htc⟩
      have heq := hunique (CoordNode.aux (f (i + 1)) c)
        ⟨hc, rfl, htc⟩
      cases heq
      rfl
  | one j b =>
      have hcontra := htz.2
      simp [t, level, truncate] at hcontra
  | enum j b =>
      have hcontra := htz.2
      simp [t, level, truncate] at hcontra

/-- The unique next selected auxiliary type determined by the
actual infinite strong picture and the given Boolean bit. -/
noncomputable def infiniteStrongPicture_auxStep
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (i : Nat) (a : AuxNode (f i))
    (ha : CoordNode.aux (f i) a ∈ S)
    (bit : Bool) : AuxNode (f (i + 1)) :=
  Classical.choose (infiniteStrongPicture_aux_lift hS i a ha bit)

theorem infiniteStrongPicture_auxStep_spec
    {S : Set CoordNode} {f : Nat → Nat} {r : CoordNode}
    (hS : InfiniteStrongPicture S f r)
    (i : Nat) (a : AuxNode (f i))
    (ha : CoordNode.aux (f i) a ∈ S)
    (bit : Bool) :
    CoordNode.aux (f (i + 1))
      (infiniteStrongPicture_auxStep hS i a ha bit) ∈ S ∧
    CoordNode.aux (f i + 1) (a.succ bit) ≤
      CoordNode.aux (f (i + 1))
        (infiniteStrongPicture_auxStep hS i a ha bit) :=
  (Classical.choose_spec (infiniteStrongPicture_aux_lift hS i a ha bit)).1

/-- The genuine all-level auxiliary canonical map of a strong picture.
Every image is proved to be in the corresponding selected layer. -/
noncomputable def infiniteAuxCanonicalMap
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r)) :
    (i : Nat) → AuxNode i →
      {b : AuxNode (f i) // CoordNode.aux (f i) b ∈ S}
  | 0, _ => ⟨r, hS.root_mem⟩
  | i + 1, a => by
      let prev := infiniteAuxCanonicalMap hS i (a.truncate i)
      let b := infiniteStrongPicture_auxStep hS i
        prev.val prev.property (a.bit i)
      have hb :=
        (infiniteStrongPicture_auxStep_spec hS i
          prev.val prev.property (a.bit i)).1
      exact ⟨b, hb⟩

@[simp] theorem infiniteAuxCanonicalMap_root
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (a : AuxNode 0) :
    (infiniteAuxCanonicalMap hS 0 a).val = r := rfl

end CoordNode
end ThreeUniformDiaries
