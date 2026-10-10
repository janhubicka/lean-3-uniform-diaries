import ThreeUniformDiaries.FiniteCoupledCanonicalMaps

/-!
# Source successor laws for the actual coupled finite canonical maps

The concrete E1 and E0 canonical maps are now constructed recursively
from completed strong pictures. These two lemmas prove their exact
one-step cone compatibility, in triangular dependence on the already
mapped parameter coordinate (E2 for E1, and E1 for E0).

Together with FiniteAuxCanonicalMapSucc they establish the genuine
successor-cone recursion for all three type coordinates, without
assuming the fields of an abstract CanonicalMap.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finiteStrongPicture_oneCanonicalMap_succ
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (i : Nat) (hi : i < k) (a : OneNode i) (c : AuxNode i) :
    CoordNode.one (f i + 1)
      ((finiteStrongPicture_oneCanonicalMap h₁ h₂ i
        (Nat.le_of_lt hi) a).val.succ
      (finiteStrongPicture_auxCanonicalMap h₂ i
        (Nat.le_of_lt hi) c).val) ≤
    CoordNode.one (f (i + 1))
      ((finiteStrongPicture_oneCanonicalMap h₁ h₂ (i + 1)
        (by omega) (a.succ c)).val) := by
  let prev := finiteStrongPicture_oneCanonicalMap h₁ h₂ i
    (Nat.le_of_lt hi) a
  let param := finiteStrongPicture_auxCanonicalMap h₂ i
    (Nat.le_of_lt hi) c
  have hstep := (finiteStrongPicture_oneStep_spec h₁ i hi
    prev.val prev.property param.val).2
  have heq :
      (finiteStrongPicture_oneCanonicalMap h₁ h₂ (i + 1)
        (by omega) (a.succ c)).val =
      finiteStrongPicture_oneStep h₁ i hi
        prev.val prev.property param.val := by
    dsimp only [finiteStrongPicture_oneCanonicalMap]
    simp only [OneNode.truncate_succ, OneNode.boundaryAux_succ]
    rfl
  change CoordNode.one (f i + 1) (prev.val.succ param.val) ≤
    CoordNode.one (f (i + 1))
      ((finiteStrongPicture_oneCanonicalMap h₁ h₂ (i + 1)
        (by omega) (a.succ c)).val)
  rw [heq]
  exact hstep

theorem finiteStrongPicture_enumCanonicalMap_succ
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (i : Nat) (hi : i < k) (a : EnumNode i) (b : OneNode i) :
    CoordNode.enum (f i + 1)
      ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
        (Nat.le_of_lt hi) a).val.succ
      (finiteStrongPicture_oneCanonicalMap h₁ h₂ i
        (Nat.le_of_lt hi) b).val) ≤
    CoordNode.enum (f (i + 1))
      ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (i + 1)
        (by omega) (a.succ b)).val) := by
  let prev := finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
    (Nat.le_of_lt hi) a
  let param := finiteStrongPicture_oneCanonicalMap h₁ h₂ i
    (Nat.le_of_lt hi) b
  have hstep := (finiteStrongPicture_enumStep_spec h₀ i hi
    prev.val prev.property param.val).2
  have heq :
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (i + 1)
        (by omega) (a.succ b)).val =
      finiteStrongPicture_enumStep h₀ i hi
        prev.val prev.property param.val := by
    dsimp only [finiteStrongPicture_enumCanonicalMap]
    simp only [EnumNode.truncate_succ, EnumNode.boundaryOne_succ]
    rfl
  change CoordNode.enum (f i + 1) (prev.val.succ param.val) ≤
    CoordNode.enum (f (i + 1))
      ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (i + 1)
        (by omega) (a.succ b)).val)
  rw [heq]
  exact hstep

end CoordNode
end ThreeUniformDiaries
