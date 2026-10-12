import ThreeUniformDiaries.RootGluedReverseStrong
import ThreeUniformDiaries.RootGluedGeneralStrong
import ThreeUniformDiaries.PrunedTypeTrees

/-!
# Synchronized E0/E1/E2 coordinates recovered from genuine scalar Milliken

Every strong scalar subtree rooted at the extra root yields three
genuine geometric InfiniteStrongPicture objects with one shared
coordinate level map. Their glued carrier is exactly the scalar
subtree's original carrier, rather than an auxiliary copy.

This is the reverse geometric component of the ATR decoder, without
any vector-strongness or meet-closure assumption.
-/

namespace ThreeUniformDiaries
namespace CoordNode

private def zeroEnumerationType : EnumNode 0 where
  triple := fun _ _ _ => false
  support := by intro i j k hbad; rfl

private theorem enumRoot_of_sort
    {S₀ : Set CoordNode} {f : Nat → Nat}
    (r : CoordNode) (hs : sort r = 0)
    (hr : level r = f 0)
    (hS : InfiniteStrongPicture S₀ f r) :
    ∃ r₀ : EnumNode (f 0),
      InfiniteStrongPicture S₀ f (.enum (f 0) r₀) := by
  cases r with
  | aux n a => simp [sort] at hs
  | one n a => simp [sort] at hs
  | enum n a =>
      have hn : n = f 0 := hr
      subst n
      exact ⟨a, hS⟩

private theorem oneRoot_of_sort
    {S₁ : Set CoordNode} {f : Nat → Nat}
    (r : CoordNode) (hs : sort r = 1)
    (hr : level r = f 0)
    (hS : InfiniteStrongPicture S₁ f r) :
    ∃ r₁ : OneNode (f 0),
      InfiniteStrongPicture S₁ f (.one (f 0) r₁) := by
  cases r with
  | aux n a => simp [sort] at hs
  | enum n a => simp [sort] at hs
  | one n a =>
      have hn : n = f 0 := hr
      subst n
      exact ⟨a, hS⟩

private theorem auxRoot_of_sort
    {S₂ : Set CoordNode} {f : Nat → Nat}
    (r : CoordNode) (hs : sort r = 2)
    (hr : level r = f 0)
    (hS : InfiniteStrongPicture S₂ f r) :
    ∃ r₂ : AuxNode (f 0),
      InfiniteStrongPicture S₂ f (.aux (f 0) r₂) := by
  cases r with
  | one n a => simp [sort] at hs
  | enum n a => simp [sort] at hs
  | aux n a =>
      have hn : n = f 0 := hr
      subst n
      exact ⟨a, hS⟩

/-- Recover all three actual coordinate strong pictures with one
shared coordinate-level map from every root-preserving scalar tree. -/
theorem millikenStrong_exists_actual_vector
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (hroot : S.root = (none : WithBot CoordNode)) :
    let f := millikenCoordinateLevels S
    ∃ (r₀ : EnumNode (f 0))
      (r₁ : OneNode (f 0))
      (r₂ : AuxNode (f 0)),
        InfiniteStrongPicture (millikenCoordinateSlice S 0) f
          (.enum (f 0) r₀) ∧
        InfiniteStrongPicture (millikenCoordinateSlice S 1) f
          (.one (f 0) r₁) ∧
        InfiniteStrongPicture (millikenCoordinateSlice S 2) f
          (.aux (f 0) r₂) := by
  let f := millikenCoordinateLevels S
  obtain ⟨r₀, hs₀, hl₀, hp₀⟩ :=
    millikenCoordinate_exists_infiniteStrong_of_root
      S hroot (.enum 0 zeroEnumerationType) rfl
  obtain ⟨r₁, hs₁, hl₁, hp₁⟩ :=
    millikenCoordinate_exists_infiniteStrong_of_root
      S hroot (.one 0 (OneNode.zero 0)) rfl
  obtain ⟨r₂, hs₂, hl₂, hp₂⟩ :=
    millikenCoordinate_exists_infiniteStrong_of_root
      S hroot (.aux 0 (AuxNode.zero 0)) rfl
  change sort r₀ = 0 at hs₀
  change sort r₁ = 1 at hs₁
  change sort r₂ = 2 at hs₂
  obtain ⟨a₀, ha₀⟩ := enumRoot_of_sort r₀ hs₀ hl₀ hp₀
  obtain ⟨a₁, ha₁⟩ := oneRoot_of_sort r₁ hs₁ hl₁ hp₁
  obtain ⟨a₂, ha₂⟩ := auxRoot_of_sort r₂ hs₂ hl₂ hp₂
  exact ⟨a₀, a₁, a₂, ha₀, ha₁, ha₂⟩

/-- Root-gluing those genuine reconstructed coordinate pictures
returns the original scalar strong-tree CARRIER exactly. -/
theorem millikenStrong_recovered_vector_carrier
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (hroot : S.root = (none : WithBot CoordNode))
    {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture (millikenCoordinateSlice S 0) f
      (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture (millikenCoordinateSlice S 1) f
      (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture (millikenCoordinateSlice S 2) f
      (.aux (f 0) r₂))
    (hf : StrictMono f) :
    (gluedVectorStrong_to_milliken h₀ h₁ h₂ hf).carrier =
        S.carrier := by
  change gluedVectorStrongCarrier h₀ h₁ h₂ = S.carrier
  ext x
  cases x with
  | none =>
      constructor
      · intro _
        have hr := S.root_mem
        rw [hroot] at hr
        exact hr
      · intro _
        exact gluedVectorStrongCarrier_root_mem h₀ h₁ h₂
  | some x =>
      cases x with
      | enum n a =>
          change some (CoordNode.enum n a) ∈
            gluedVectorStrongCarrier h₀ h₁ h₂ ↔
            some (CoordNode.enum n a) ∈ S.carrier
          rw [gluedVectorStrongCarrier_enum_iff h₀ h₁ h₂ n a]
          simp [millikenCoordinateSlice, TypedVectorSubset.ofGlued, sort]
      | one n a =>
          change some (CoordNode.one n a) ∈
            gluedVectorStrongCarrier h₀ h₁ h₂ ↔
            some (CoordNode.one n a) ∈ S.carrier
          rw [gluedVectorStrongCarrier_one_iff h₀ h₁ h₂ n a]
          simp [millikenCoordinateSlice, TypedVectorSubset.ofGlued, sort]
      | aux n a =>
          change some (CoordNode.aux n a) ∈
            gluedVectorStrongCarrier h₀ h₁ h₂ ↔
            some (CoordNode.aux n a) ∈ S.carrier
          rw [gluedVectorStrongCarrier_aux_iff h₀ h₁ h₂ n a]
          simp [millikenCoordinateSlice, TypedVectorSubset.ofGlued, sort]

end CoordNode
end ThreeUniformDiaries
