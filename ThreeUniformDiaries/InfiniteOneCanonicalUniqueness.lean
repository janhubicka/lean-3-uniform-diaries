import ThreeUniformDiaries.InfiniteAuxCanonicalUniqueness

/-!
# Uniqueness of the genuine E1 canonical map from successor cones

Once the E2 parameter map is fixed, each singleton-type successor
is determined by its full E2 boundary parameter and one strong
successor cone. Any E1 candidate with the same root, whose values
belong to the chosen strong singleton picture and respect these
cones, is equal to the concrete recursive E1 map.

This triangular uniqueness principle is intended for the
geometric composition theorem.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteOneCanonicalMap_unique_of_cones
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (G₂ : (i : Nat) → AuxNode i → AuxNode (f i))
    (G₁ : (i : Nat) → OneNode i → OneNode (f i))
    (hG₂ : ∀ i (c : AuxNode i),
      G₂ i c = (infiniteAuxCanonicalMap h₂ i c).val)
    (hmem : ∀ i (a : OneNode i),
      CoordNode.one (f i) (G₁ i a) ∈ S₁)
    (hroot : ∀ a : OneNode 0, G₁ 0 a = r₁)
    (hsucc : ∀ i (a : OneNode i) (c : AuxNode i),
      CoordNode.one (f i + 1) ((G₁ i a).succ (G₂ i c)) ≤
        CoordNode.one (f (i + 1)) (G₁ (i + 1) (a.succ c))) :
    ∀ i (a : OneNode i),
      G₁ i a = (infiniteOneCanonicalMap h₁ h₂ i a).val := by
  intro n
  induction n with
  | zero =>
      intro a
      exact hroot a
  | succ i ih =>
      intro a
      let prev : OneNode i := a.truncate i
      let c : AuxNode i := a.boundaryAux i
      have hsrc : prev.succ c = a :=
        OneNode.succ_truncate_boundary a
      have hparent : G₁ i prev =
          (infiniteOneCanonicalMap h₁ h₂ i prev).val := ih prev
      have hconeG :
          CoordNode.one (f i + 1)
              ((infiniteOneCanonicalMap h₁ h₂ i prev).val.succ
                (infiniteAuxCanonicalMap h₂ i c).val) ≤
          CoordNode.one (f (i + 1)) (G₁ (i + 1) a) := by
        have h := hsucc i prev c
        rw [hparent, hG₂ i c, hsrc] at h
        exact h
      have hconeC :
          CoordNode.one (f i + 1)
              ((infiniteOneCanonicalMap h₁ h₂ i prev).val.succ
                (infiniteAuxCanonicalMap h₂ i c).val) ≤
          CoordNode.one (f (i + 1))
              (infiniteOneCanonicalMap h₁ h₂ (i + 1) a).val := by
        have h := infiniteOneCanonicalMap_succ h₁ h₂ i prev c
        rw [hsrc] at h
        exact h
      obtain ⟨b, hb, unique⟩ :=
        infiniteStrongPicture_one_lift h₁ i
          (infiniteOneCanonicalMap h₁ h₂ i prev).val
          (infiniteOneCanonicalMap h₁ h₂ i prev).property
          (infiniteAuxCanonicalMap h₂ i c).val
      have hG : G₁ (i + 1) a = b :=
        unique (G₁ (i + 1) a)
          ⟨hmem (i + 1) a, hconeG⟩
      have hC :
          (infiniteOneCanonicalMap h₁ h₂ (i + 1) a).val = b :=
        unique (infiniteOneCanonicalMap h₁ h₂ (i + 1) a).val
          ⟨(infiniteOneCanonicalMap h₁ h₂ (i + 1) a).property,
            hconeC⟩
      exact hG.trans hC.symm

end CoordNode
end ThreeUniformDiaries
