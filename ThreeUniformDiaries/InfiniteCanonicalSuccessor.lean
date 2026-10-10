import ThreeUniformDiaries.InfiniteCanonicalCoupled

/-!
# Exact successor-cone recursions for actual infinite canonical maps

The all-level maps of InfiniteCanonicalCoupled are recursively
constructed from the geometric unique-child property of the
coordinate strong pictures. Their source successors are therefore
mapped to the prescribed ambient immediate-successor cone of the
previously mapped node, with the lower coordinate providing the
successor parameter.

These are concrete geometric facts, not axioms postulated as fields
of the abstract CanonicalMap structure. They are the induction input
for infinite restriction compatibility, strong-map meet preservation
and canonical-map composition.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem infiniteAuxCanonicalMap_succ
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (i : Nat) (a : AuxNode i) (bit : Bool) :
    CoordNode.aux (f i + 1)
      ((infiniteAuxCanonicalMap hS i a).val.succ bit) ≤
    CoordNode.aux (f (i + 1))
      ((infiniteAuxCanonicalMap hS (i + 1) (a.succ bit)).val) := by
  let prev := infiniteAuxCanonicalMap hS i a
  have hstep :=
    (infiniteStrongPicture_auxStep_spec hS i
      prev.val prev.property bit).2
  have heq :
      (infiniteAuxCanonicalMap hS (i + 1) (a.succ bit)).val =
      infiniteStrongPicture_auxStep hS i
        prev.val prev.property bit := by
    dsimp only [infiniteAuxCanonicalMap]
    simp only [AuxNode.truncate_succ, AuxNode.succ_new]
    rfl
  change CoordNode.aux (f i + 1) (prev.val.succ bit) ≤
    CoordNode.aux (f (i + 1))
      ((infiniteAuxCanonicalMap hS (i + 1) (a.succ bit)).val)
  rw [heq]
  exact hstep

theorem infiniteOneCanonicalMap_succ
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (i : Nat) (a : OneNode i) (c : AuxNode i) :
    CoordNode.one (f i + 1)
      ((infiniteOneCanonicalMap h₁ h₂ i a).val.succ
       (infiniteAuxCanonicalMap h₂ i c).val) ≤
    CoordNode.one (f (i + 1))
      ((infiniteOneCanonicalMap h₁ h₂ (i + 1) (a.succ c)).val) := by
  let prev := infiniteOneCanonicalMap h₁ h₂ i a
  let param := infiniteAuxCanonicalMap h₂ i c
  have hstep :=
    (infiniteStrongPicture_oneStep_spec h₁ i
      prev.val prev.property param.val).2
  have heq :
      (infiniteOneCanonicalMap h₁ h₂ (i + 1) (a.succ c)).val =
        infiniteStrongPicture_oneStep h₁ i
          prev.val prev.property param.val := by
    dsimp only [infiniteOneCanonicalMap]
    simp only [OneNode.truncate_succ, OneNode.boundaryAux_succ]
    rfl
  change CoordNode.one (f i + 1) (prev.val.succ param.val) ≤
    CoordNode.one (f (i + 1))
      ((infiniteOneCanonicalMap h₁ h₂ (i + 1) (a.succ c)).val)
  rw [heq]
  exact hstep

theorem infiniteEnumCanonicalMap_succ
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (i : Nat) (a : EnumNode i) (b : OneNode i) :
    CoordNode.enum (f i + 1)
      ((infiniteEnumCanonicalMap h₀ h₁ h₂ i a).val.succ
       (infiniteOneCanonicalMap h₁ h₂ i b).val) ≤
    CoordNode.enum (f (i + 1))
      ((infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) (a.succ b)).val) := by
  let prev := infiniteEnumCanonicalMap h₀ h₁ h₂ i a
  let param := infiniteOneCanonicalMap h₁ h₂ i b
  have hstep :=
    (infiniteStrongPicture_enumStep_spec h₀ i
      prev.val prev.property param.val).2
  have heq :
      (infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) (a.succ b)).val =
        infiniteStrongPicture_enumStep h₀ i
          prev.val prev.property param.val := by
    dsimp only [infiniteEnumCanonicalMap]
    simp only [EnumNode.truncate_succ, EnumNode.boundaryOne_succ]
    rfl
  change CoordNode.enum (f i + 1) (prev.val.succ param.val) ≤
    CoordNode.enum (f (i + 1))
      ((infiniteEnumCanonicalMap h₀ h₁ h₂ (i + 1) (a.succ b)).val)
  rw [heq]
  exact hstep

end CoordNode
end ThreeUniformDiaries
