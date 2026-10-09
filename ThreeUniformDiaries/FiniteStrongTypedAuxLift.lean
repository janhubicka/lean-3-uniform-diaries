import ThreeUniformDiaries.FiniteSelectedSuccessorUnique

/-!
# Canonical auxiliary successor in a completed finite strong picture

A finite strong picture is a set of typed coordinate nodes. For the
auxiliary coordinate, the abstract unique successor in an ambient child
cone can be presented as an AuxNode on the next selected level.

This is the first constructive (rather than candidate-only) interface
for defining the canonical maps f₂^S in the manuscript. It applies
to every auxiliary node retained in S, including non-prescribed
intermediate nodes, and to both possible source successor bits.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finiteStrongPicture_aux_lift
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (i : Nat) (hi : i < k)
    (a : AuxNode (f i))
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
  rcases hS with ⟨_, _, _, _, _, _, hchildren⟩
  obtain ⟨z, ⟨hz, hzlevel, htz⟩, hunique⟩ :=
    hchildren i hi p ha rfl t hcover
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

/-- The selected auxiliary successor can now be chosen constructively
for all retained nodes, with the defining membership and cone facts. -/
noncomputable def finiteStrongPicture_auxStep
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat} {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (i : Nat) (hi : i < k)
    (a : AuxNode (f i))
    (ha : CoordNode.aux (f i) a ∈ S)
    (bit : Bool) :
    AuxNode (f (i + 1)) :=
  Classical.choose (finiteStrongPicture_aux_lift hS i hi a ha bit)

theorem finiteStrongPicture_auxStep_spec
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat} {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (i : Nat) (hi : i < k)
    (a : AuxNode (f i))
    (ha : CoordNode.aux (f i) a ∈ S)
    (bit : Bool) :
    CoordNode.aux (f (i + 1))
        (finiteStrongPicture_auxStep hS i hi a ha bit) ∈ S ∧
      CoordNode.aux (f i + 1) (a.succ bit) ≤
        CoordNode.aux (f (i + 1))
          (finiteStrongPicture_auxStep hS i hi a ha bit) :=
  Classical.choose_spec (finiteStrongPicture_aux_lift hS i hi a ha bit)

end CoordNode
end ThreeUniformDiaries
