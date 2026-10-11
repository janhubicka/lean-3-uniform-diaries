import ThreeUniformDiaries.InfiniteOneCanonicalUniqueness

/-!
# Uniqueness of genuine E0 enumeration canonical maps

Once the E1 singleton parameter map is identified, the strong
enumeration coordinate picks a unique representative in each full
singleton-type successor cone. A candidate E0 map landing in the
strong picture, fixing the root and respecting these cones must be
the actual recursive enumeration canonical map.

Together with E2 and E1 uniqueness, this is the triangular
geometric identity principle needed to finish the canonical
composition lemma.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteEnumCanonicalMap_unique_of_cones
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (G₁ : (i : Nat) → OneNode i → OneNode (f i))
    (G₀ : (i : Nat) → EnumNode i → EnumNode (f i))
    (hG₁ : ∀ i (b : OneNode i),
      G₁ i b = (infiniteOneCanonicalMap h₁ h₂ i b).val)
    (hmem : ∀ i (a : EnumNode i),
      CoordNode.enum (f i) (G₀ i a) ∈ S₀)
    (hroot : ∀ a : EnumNode 0, G₀ 0 a = r₀)
    (hsucc : ∀ i (a : EnumNode i) (b : OneNode i),
      CoordNode.enum (f i + 1) ((G₀ i a).succ (G₁ i b)) ≤
        CoordNode.enum (f (i + 1)) (G₀ (i + 1) (a.succ b))) :
    ∀ i (a : EnumNode i),
      G₀ i a = (infiniteEnumCanonicalMap h₀ h₁ h₂ i a).val := by
  intro n
  induction n with
  | zero =>
      intro a
      exact hroot a
  | succ i ih =>
      intro a
      let prev : EnumNode i := a.truncate i
      let b : OneNode i := a.boundaryOne i
      have hsrc : prev.succ b = a :=
        EnumNode.succ_truncate_boundary a
      have hparent : G₀ i prev =
          (infiniteEnumCanonicalMap h₀ h₁ h₂ i prev).val := ih prev
      have hconeG :
          CoordNode.enum (f i + 1)
              ((infiniteEnumCanonicalMap h₀ h₁ h₂ i prev).val.succ
                (infiniteOneCanonicalMap h₁ h₂ i b).val) ≤
          CoordNode.enum (f (i + 1)) (G₀ (i + 1) a) := by
        have h := hsucc i prev b
        rw [hparent, hG₁ i b, hsrc] at h
        exact h
      have hconeC :
          CoordNode.enum (f i + 1)
              ((infiniteEnumCanonicalMap h₀ h₁ h₂ i prev).val.succ
                (infiniteOneCanonicalMap h₁ h₂ i b).val) ≤
          CoordNode.enum (f (i + 1))
              (infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) a).val := by
        have h := infiniteEnumCanonicalMap_succ h₀ h₁ h₂ i prev b
        rw [hsrc] at h
        exact h
      obtain ⟨c, hc, unique⟩ :=
        infiniteStrongPicture_enum_lift h₀ i
          (infiniteEnumCanonicalMap h₀ h₁ h₂ i prev).val
          (infiniteEnumCanonicalMap h₀ h₁ h₂ i prev).property
          (infiniteOneCanonicalMap h₁ h₂ i b).val
      have hG : G₀ (i + 1) a = c :=
        unique (G₀ (i + 1) a)
          ⟨hmem (i + 1) a, hconeG⟩
      have hC :
          (infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) a).val = c :=
        unique (infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) a).val
          ⟨(infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) a).property,
            hconeC⟩
      exact hG.trans hC.symm

end CoordNode
end ThreeUniformDiaries
