import ThreeUniformDiaries.RelativeLevelPopulation

/-!
# An injective numerical code respecting the length of K_I nodes

Each finite enumeration node at level k has a finite ordinal in
EnumNode (k+1). By placing all such ordinals in consecutive disjoint
integer blocks, we obtain an injective code of relative K_I nodes
whose values are strictly ordered between different lengths.

The *range* of this code will next be enumerated increasingly via
Nat.Subtype.orderIsoOfNat. This avoids assuming an arbitrary
bijection already respects the lengths.
-/

namespace ThreeUniformDiaries

/-- The number of possible enumerated hypergraphs of length k+1. -/
noncomputable def enumerationLevelCapacity (k : Nat) : Nat :=
  Fintype.card (EnumNode (k + 1))

/-- Every length has at least one enumeration. -/
theorem enumerationLevelCapacity_pos
    {n : Nat} (I : EnumNode n) (k : Nat) :
    0 < enumerationLevelCapacity k := by
  classical
  have h : Nonempty (EnumNode (k + 1)) := ⟨I.truncate (k + 1)⟩
  exact Fintype.card_pos_iff.mpr h

/-- Beginning of the integer block used for nodes at level k. -/
noncomputable def enumerationLevelStart : Nat → Nat
  | 0 => 0
  | k + 1 => enumerationLevelStart k + enumerationLevelCapacity k

theorem enumerationLevelStart_mono :
    Monotone enumerationLevelStart := by
  intro k l hkl
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hl ih =>
      change enumerationLevelStart k ≤
        enumerationLevelStart l + enumerationLevelCapacity l
      omega

theorem enumerationLevelStart_succ
    {n : Nat} (I : EnumNode n) (k : Nat) :
    enumerationLevelStart k < enumerationLevelStart (k + 1) := by
  change enumerationLevelStart k <
    enumerationLevelStart k + enumerationLevelCapacity k
  have hp := enumerationLevelCapacity_pos I k
  omega

/-- Its ordinal within the finite block of its enumeration length. -/
noncomputable def relativeBranchLevelOrdinal
    {n : Nat} (I : EnumNode n) (A : RelativeBranchNode I) :
    Fin (enumerationLevelCapacity A.val.last) :=
  (Fintype.equivFin (EnumNode (A.val.last + 1))) A.val.enumeration

/-- The global length-first numerical code, with gaps for finite
enumerations that are not compatible with the fixed I. -/
noncomputable def relativeBranchNumericCode
    {n : Nat} (I : EnumNode n) (A : RelativeBranchNode I) : Nat :=
  enumerationLevelStart A.val.last + (relativeBranchLevelOrdinal I A).val

/-- All codes of smaller-length nodes precede every code of a
larger-length node, irrespective of their finite enumeration bits. -/
theorem relativeBranchNumericCode_lt_of_last_lt
    {n : Nat} (I : EnumNode n) {A B : RelativeBranchNode I}
    (hlevel : A.val.last < B.val.last) :
    relativeBranchNumericCode I A < relativeBranchNumericCode I B := by
  have hstart : enumerationLevelStart (A.val.last + 1) ≤
      enumerationLevelStart B.val.last :=
    enumerationLevelStart_mono (by omega)
  have hordinal : (relativeBranchLevelOrdinal I A).val <
      enumerationLevelCapacity A.val.last :=
    (relativeBranchLevelOrdinal I A).isLt
  change enumerationLevelStart A.val.last +
      (relativeBranchLevelOrdinal I A).val <
    enumerationLevelStart B.val.last +
      (relativeBranchLevelOrdinal I B).val
  have hstep : enumerationLevelStart (A.val.last + 1) =
      enumerationLevelStart A.val.last +
        enumerationLevelCapacity A.val.last := rfl
  omega

/-- Within a single length, the ordinal is injective; together with
disjoint integer blocks this makes the global code injective. -/
theorem relativeBranchNumericCode_injective
    {n : Nat} (I : EnumNode n) :
    Function.Injective (relativeBranchNumericCode I) := by
  intro A B hcode
  have hlevel : A.val.last = B.val.last := by
    by_contra heq
    rcases lt_or_gt_of_ne heq with hab | hba
    · have hlt := relativeBranchNumericCode_lt_of_last_lt I hab
      omega
    · have hlt := relativeBranchNumericCode_lt_of_last_lt I hba
      omega
  rcases A with ⟨⟨k, E⟩, hA⟩
  rcases B with ⟨⟨l, F⟩, hB⟩
  change k = l at hlevel
  subst l
  have hEqOrdinal :
      (Fintype.equivFin (EnumNode (k + 1))) E =
      (Fintype.equivFin (EnumNode (k + 1))) F := by
    apply Fin.ext
    have hc := hcode
    change enumerationLevelStart k +
        ((Fintype.equivFin (EnumNode (k + 1))) E).val =
      enumerationLevelStart k +
        ((Fintype.equivFin (EnumNode (k + 1))) F).val at hc
    omega
  have hEF : E = F :=
    (Fintype.equivFin (EnumNode (k + 1))).injective hEqOrdinal
  cases hEF
  rfl

end ThreeUniformDiaries
