import ThreeUniformDiaries.FiniteCanonicalFixedRoot
import ThreeUniformDiaries.FiniteAuxCanonicalMapSucc
import ThreeUniformDiaries.FiniteCoupledCanonicalMapSucc

/-!
# Concrete canonical-map fixed-prefix induction steps

Between consecutive fixed levels f(i)=i and f(i+1)=i+1 no ambient
levels are skipped. A canonical-map successor therefore has exactly
the source successor as image, once the predecessor and triangular
parameter have their prescribed images.

The three lemmas explicitly isolate the induction from T2 through T1
to T0, using the ACTUAL recursively constructed finite maps and their
checked child-cone laws, not the abstract CanonicalMap structure.
-/

namespace ThreeUniformDiaries
namespace CoordNode


/-- A coordinate-level successor allows transporting equalities without
casting dependent auxiliary nodes between distinct level indices. -/
private def auxSuccessorNode (bit : Bool) (x : CoordNode) : CoordNode :=
  match x with
  | .aux n a => .aux (n + 1) (a.succ bit)
  | other => zeroChild other

private def oneSuccessorNode (x y : CoordNode) : CoordNode :=
  match x, y with
  | .one n a, .aux m b =>
      if h : n = m then .one (n + 1) (a.succ (h.symm ▸ b))
      else zeroChild x
  | _, _ => zeroChild x

private def enumSuccessorNode (x y : CoordNode) : CoordNode :=
  match x, y with
  | .enum n a, .one m b =>
      if h : n = m then .enum (n + 1) (a.succ (h.symm ▸ b))
      else zeroChild x
  | _, _ => zeroChild x

theorem finiteAuxCanonicalMap_fixed_step
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : AuxNode (f 0)}
    (hS : FiniteStrongPicture S f k (.aux (f 0) r))
    (i : Nat) (hi : i < k)
    (hfi : f i = i) (hfi1 : f (i + 1) = i + 1)
    (a : AuxNode (i + 1))
    (hprev :
      CoordNode.aux (f i)
        (finiteStrongPicture_auxCanonicalMap hS i
          (Nat.le_of_lt hi) (a.truncate i)).val =
      CoordNode.aux i (a.truncate i)) :
    CoordNode.aux (f (i + 1))
      (finiteStrongPicture_auxCanonicalMap hS (i + 1)
        (by omega) a).val =
      CoordNode.aux (i + 1) a := by
  have hcone := finiteStrongPicture_auxCanonicalMap_succ
    hS i hi (a.truncate i) (a.bit i)
  rw [AuxNode.succ_truncate_new] at hcone
  have hsucc :
      CoordNode.aux (f i + 1)
        ((finiteStrongPicture_auxCanonicalMap hS i
          (Nat.le_of_lt hi) (a.truncate i)).val.succ (a.bit i)) =
      CoordNode.aux (i + 1) a := by
    have hc := congrArg (auxSuccessorNode (a.bit i)) hprev
    simpa [auxSuccessorNode, AuxNode.succ_truncate_new] using hc
  rw [hsucc] at hcone
  have hlev :
      level (CoordNode.aux (i + 1) a) =
        level (CoordNode.aux (f (i + 1))
          (finiteStrongPicture_auxCanonicalMap hS (i + 1)
            (by omega) a).val) := by
    simp [hfi1, level]
  exact (eq_of_le_of_level_eq hcone hlev).symm


theorem finiteOneCanonicalMap_fixed_step
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (i : Nat) (hi : i < k)
    (hfi : f i = i) (hfi1 : f (i + 1) = i + 1)
    (a : OneNode (i + 1))
    (hprev :
      CoordNode.one (f i)
        (finiteStrongPicture_oneCanonicalMap h₁ h₂ i
          (Nat.le_of_lt hi) (a.truncate i)).val =
      CoordNode.one i (a.truncate i))
    (hparam :
      CoordNode.aux (f i)
        (finiteStrongPicture_auxCanonicalMap h₂ i
          (Nat.le_of_lt hi) (a.boundaryAux i)).val =
      CoordNode.aux i (a.boundaryAux i)) :
    CoordNode.one (f (i + 1))
      (finiteStrongPicture_oneCanonicalMap h₁ h₂ (i + 1)
        (by omega) a).val =
      CoordNode.one (i + 1) a := by
  have hcone := finiteStrongPicture_oneCanonicalMap_succ
    h₁ h₂ i hi (a.truncate i) (a.boundaryAux i)
  rw [OneNode.succ_truncate_boundary] at hcone
  have hsucc :
      CoordNode.one (f i + 1)
        ((finiteStrongPicture_oneCanonicalMap h₁ h₂ i
          (Nat.le_of_lt hi) (a.truncate i)).val.succ
        (finiteStrongPicture_auxCanonicalMap h₂ i
          (Nat.le_of_lt hi) (a.boundaryAux i)).val) =
      CoordNode.one (i + 1) a := by
    have hc := congrArg₂ oneSuccessorNode hprev hparam
    simpa [oneSuccessorNode, OneNode.succ_truncate_boundary] using hc
  rw [hsucc] at hcone
  have hlev :
      level (CoordNode.one (i + 1) a) =
        level (CoordNode.one (f (i + 1))
          (finiteStrongPicture_oneCanonicalMap h₁ h₂ (i + 1)
            (by omega) a).val) := by
    simp [hfi1, level]
  exact (eq_of_le_of_level_eq hcone hlev).symm


theorem finiteEnumCanonicalMap_fixed_step
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (i : Nat) (hi : i < k)
    (hfi : f i = i) (hfi1 : f (i + 1) = i + 1)
    (a : EnumNode (i + 1))
    (hprev :
      CoordNode.enum (f i)
        (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
          (Nat.le_of_lt hi) (a.truncate i)).val =
      CoordNode.enum i (a.truncate i))
    (hparam :
      CoordNode.one (f i)
        (finiteStrongPicture_oneCanonicalMap h₁ h₂ i
          (Nat.le_of_lt hi) (a.boundaryOne i)).val =
      CoordNode.one i (a.boundaryOne i)) :
    CoordNode.enum (f (i + 1))
      (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (i + 1)
        (by omega) a).val =
      CoordNode.enum (i + 1) a := by
  have hcone := finiteStrongPicture_enumCanonicalMap_succ
    h₀ h₁ h₂ i hi (a.truncate i) (a.boundaryOne i)
  rw [EnumNode.succ_truncate_boundary] at hcone
  have hsucc :
      CoordNode.enum (f i + 1)
        ((finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
          (Nat.le_of_lt hi) (a.truncate i)).val.succ
        (finiteStrongPicture_oneCanonicalMap h₁ h₂ i
          (Nat.le_of_lt hi) (a.boundaryOne i)).val) =
      CoordNode.enum (i + 1) a := by
    have hc := congrArg₂ enumSuccessorNode hprev hparam
    simpa [enumSuccessorNode, EnumNode.succ_truncate_boundary] using hc
  rw [hsucc] at hcone
  have hlev :
      level (CoordNode.enum (i + 1) a) =
        level (CoordNode.enum (f (i + 1))
          (finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ (i + 1)
            (by omega) a).val) := by
    simp [hfi1, level]
  exact (eq_of_le_of_level_eq hcone hlev).symm


end CoordNode
end ThreeUniformDiaries
