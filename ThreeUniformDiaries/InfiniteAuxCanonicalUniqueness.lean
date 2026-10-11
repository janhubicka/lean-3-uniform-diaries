import ThreeUniformDiaries.InfiniteCanonicalSuccessor

/-!
# Uniqueness of the genuine auxiliary canonical map

A candidate E2 map that lands in a given strong coordinate picture,
agrees with its root, and always extends the prescribed Boolean
successor cone must be the actual recursively chosen canonical E2 map.

This isolates the final geometric composition argument from the
construction of the protected relative strong completion. No
algebraic CanonicalMap compatibility is assumed of the candidate.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxCanonicalMap_unique_of_cones
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (G : (i : Nat) → AuxNode i → AuxNode (f i))
    (hmem : ∀ i (a : AuxNode i),
      CoordNode.aux (f i) (G i a) ∈ S)
    (hroot : ∀ a : AuxNode 0, G 0 a = r)
    (hsucc : ∀ i (a : AuxNode i) (b : Bool),
      CoordNode.aux (f i + 1) ((G i a).succ b) ≤
        CoordNode.aux (f (i + 1)) (G (i + 1) (a.succ b))) :
    ∀ i (a : AuxNode i),
      G i a = (infiniteAuxCanonicalMap hS i a).val := by
  intro n
  induction n with
  | zero =>
      intro a
      exact hroot a
  | succ i ih =>
      intro a
      let prev : AuxNode i := a.truncate i
      let bit : Bool := a.bit i
      have hsrc : prev.succ bit = a :=
        AuxNode.succ_truncate_new a
      have hparent : G i prev =
          (infiniteAuxCanonicalMap hS i prev).val := ih prev
      have hGcone :
          CoordNode.aux (f i + 1)
              ((infiniteAuxCanonicalMap hS i prev).val.succ bit) ≤
          CoordNode.aux (f (i + 1)) (G (i + 1) a) := by
        have h := hsucc i prev bit
        rw [hparent, hsrc] at h
        exact h
      have hCcone :
          CoordNode.aux (f i + 1)
              ((infiniteAuxCanonicalMap hS i prev).val.succ bit) ≤
          CoordNode.aux (f (i + 1))
              (infiniteAuxCanonicalMap hS (i + 1) a).val := by
        have h := infiniteAuxCanonicalMap_succ hS i prev bit
        rw [hsrc] at h
        exact h
      obtain ⟨b, hb, unique⟩ :=
        infiniteStrongPicture_aux_lift hS i
          (infiniteAuxCanonicalMap hS i prev).val
          (infiniteAuxCanonicalMap hS i prev).property bit
      have hG :
          G (i + 1) a = b :=
        unique (G (i + 1) a) ⟨hmem (i + 1) a, hGcone⟩
      have hC :
          (infiniteAuxCanonicalMap hS (i + 1) a).val = b :=
        unique (infiniteAuxCanonicalMap hS (i + 1) a).val
          ⟨(infiniteAuxCanonicalMap hS (i + 1) a).property, hCcone⟩
      exact hG.trans hC.symm

end CoordNode
end ThreeUniformDiaries
