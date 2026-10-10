import ThreeUniformDiaries.InfiniteCanonicalSuccessor
import ThreeUniformDiaries.InfiniteCanonicalInjectivity
import ThreeUniformDiaries.DistinctChildConeMeets
import ThreeUniformDiaries.VectorTree

/-!
# Exact first-disagreement meets in E1 and E0 infinite canonical maps

At a fixed source node, two distinct source successor parameters
are sent to distinct immediate ambient child cones above the
same selected target parent. Their genuine canonical images thus
meet exactly at that parent, even across skipped target levels.

The key ingredients are the checked infinite successor-cone
equations, injected lower-coordinate parameters, and the existing
general distinct-child-cone meet theorem. These geometric statements
are needed to prove the meet-closure of canonical images in the
manuscript's strong-subtree composition lemma.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteOneCanonicalMap_distinct_child_meet
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (n : Nat) (a : OneNode n)
    (b c : AuxNode n) (hbc : b ≠ c) :
    meet
      (.one (f (n + 1))
        (infiniteOneCanonicalMap h₁ h₂ (n + 1) (a.succ b)).val)
      (.one (f (n + 1))
        (infiniteOneCanonicalMap h₁ h₂ (n + 1) (a.succ c)).val)
      =
      .one (f n) (infiniteOneCanonicalMap h₁ h₂ n a).val := by
  let q := (infiniteOneCanonicalMap h₁ h₂ n a).val
  let bb := (infiniteAuxCanonicalMap h₂ n b).val
  let cc := (infiniteAuxCanonicalMap h₂ n c).val
  let p : CoordNode := .one (f n) q
  let t : CoordNode := .one (f n + 1) (q.succ bb)
  let u : CoordNode := .one (f n + 1) (q.succ cc)
  let x : CoordNode :=
    .one (f (n + 1))
      (infiniteOneCanonicalMap h₁ h₂ (n + 1) (a.succ b)).val
  let y : CoordNode :=
    .one (f (n + 1))
      (infiniteOneCanonicalMap h₁ h₂ (n + 1) (a.succ c)).val
  have hpt : p ≤ t := by
    refine ⟨Nat.le_succ _, ?_⟩
    change CoordNode.one (f n) ((q.succ bb).truncate (f n)) = p
    simp [p]
  have hpu : p ≤ u := by
    refine ⟨Nat.le_succ _, ?_⟩
    change CoordNode.one (f n) ((q.succ cc).truncate (f n)) = p
    simp [p]
  have hcovt : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
    rfl
  have hcovu : p ⋖ u := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpu
    rfl
  have htu : t ≠ u := by
    intro h
    change CoordNode.one (f n + 1) (q.succ bb) =
      CoordNode.one (f n + 1) (q.succ cc) at h
    have heq : q.succ bb = q.succ cc := by
      injection h
    have hbiteq : bb = cc := by
      have hv := congrArg
        (fun z : OneNode (f n + 1) => z.boundaryAux (f n)) heq
      simpa using hv
    have hsource : b = c :=
      (infiniteAuxCanonicalMap_injective h₂ hf n) hbiteq
    exact hbc hsource
  have htx : t ≤ x := infiniteOneCanonicalMap_succ h₁ h₂ n a b
  have huy : u ≤ y := infiniteOneCanonicalMap_succ h₁ h₂ n a c
  exact meet_descendants_distinct_children
    p t u x y hcovt hcovu htu htx huy

theorem infiniteEnumCanonicalMap_distinct_child_meet
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (n : Nat) (a : EnumNode n)
    (b c : OneNode n) (hbc : b ≠ c) :
    meet
      (.enum (f (n + 1))
        (infiniteEnumCanonicalMap h₀ h₁ h₂ (n + 1) (a.succ b)).val)
      (.enum (f (n + 1))
        (infiniteEnumCanonicalMap h₀ h₁ h₂ (n + 1) (a.succ c)).val)
      =
      .enum (f n) (infiniteEnumCanonicalMap h₀ h₁ h₂ n a).val := by
  let q := (infiniteEnumCanonicalMap h₀ h₁ h₂ n a).val
  let bb := (infiniteOneCanonicalMap h₁ h₂ n b).val
  let cc := (infiniteOneCanonicalMap h₁ h₂ n c).val
  let p : CoordNode := .enum (f n) q
  let t : CoordNode := .enum (f n + 1) (q.succ bb)
  let u : CoordNode := .enum (f n + 1) (q.succ cc)
  let x : CoordNode :=
    .enum (f (n + 1))
      (infiniteEnumCanonicalMap h₀ h₁ h₂ (n + 1) (a.succ b)).val
  let y : CoordNode :=
    .enum (f (n + 1))
      (infiniteEnumCanonicalMap h₀ h₁ h₂ (n + 1) (a.succ c)).val
  have hpt : p ≤ t := by
    refine ⟨Nat.le_succ _, ?_⟩
    change CoordNode.enum (f n) ((q.succ bb).truncate (f n)) = p
    simp [p]
  have hpu : p ≤ u := by
    refine ⟨Nat.le_succ _, ?_⟩
    change CoordNode.enum (f n) ((q.succ cc).truncate (f n)) = p
    simp [p]
  have hcovt : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
    rfl
  have hcovu : p ⋖ u := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpu
    rfl
  have htu : t ≠ u := by
    intro h
    change CoordNode.enum (f n + 1) (q.succ bb) =
      CoordNode.enum (f n + 1) (q.succ cc) at h
    have heq : q.succ bb = q.succ cc := by
      injection h
    have hbiteq : bb = cc := by
      have hv := congrArg
        (fun z : EnumNode (f n + 1) => z.boundaryOne (f n)) heq
      simpa using hv
    have hsource : b = c :=
      (infiniteOneCanonicalMap_injective h₁ h₂ hf n) hbiteq
    exact hbc hsource
  have htx : t ≤ x := infiniteEnumCanonicalMap_succ h₀ h₁ h₂ n a b
  have huy : u ≤ y := infiniteEnumCanonicalMap_succ h₀ h₁ h₂ n a c
  exact meet_descendants_distinct_children
    p t u x y hcovt hcovu htu htx huy

end CoordNode
end ThreeUniformDiaries
