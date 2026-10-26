import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Causal dependence of the literal diary lexicographic comparator

The manuscript's LexEarlier H a b for a < b is determined entirely
by the columns whose SECOND vertex lies strictly below a. In
particular, the choice of marker-one or marker-two edge (1,a,b)
or (2,a,b) cannot influence the lexicographic decision it is
supposed to represent.

This is a purely structural theorem for arbitrary ordered ternary
edge predicates. It assumes no diary axioms and does not assert that
the simultaneous cross-branch V3 orientation and V1/V2 stability
constraints have a solution. It isolates the non-self-referential
part of the remaining marker-choice construction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- All ordered-ternary columns with middle coordinate strictly below
a agree, even for formally non-increasing triples. -/
def MiddleColumnAgreementBelow
    (H K : Ordered3Graph Nat) (a : Nat) : Prop :=
  ∀ (x y z : Nat), y < a → (H.edge x y z ↔ K.edge x y z)

/-- Equality of singleton-type tests up to a cut l <= a depends only
on middle-coordinate columns below a. -/
theorem middleColumn_sameOneType_iff
    (H K : Ordered3Graph Nat)
    (a l u v : Nat)
    (hCol : MiddleColumnAgreementBelow H K a)
    (hla : l ≤ a) :
    H.SameOneTypeBelow l u v ↔
      K.SameOneTypeBelow l u v := by
  constructor
  · intro h x y hxy hyl
    have hu := hCol x y u (by omega)
    have hv := hCol x y v (by omega)
    exact hu.symm.trans ((h hxy hyl).trans hv)
  · intro h x y hxy hyl
    have hu := hCol x y u (by omega)
    have hv := hCol x y v (by omega)
    exact hu.trans ((h hxy hyl).trans hv.symm)

/-- The auxiliary type of two pointed pairs (m,u),(m,v) at
any cut l <= m < a depends only on columns below a. -/
theorem middleColumn_sameAuxPointed_iff
    (H K : Ordered3Graph Nat)
    (a m l u v : Nat)
    (hCol : MiddleColumnAgreementBelow H K a)
    (hma : m < a) :
    H.SameAuxTypeBelow l m u m v ↔
      K.SameAuxTypeBelow l m u m v := by
  constructor
  · intro h x hxl
    have hu := hCol x m u hma
    have hv := hCol x m v hma
    exact hu.symm.trans ((h hxl).trans hv)
  · intro h x hxl
    have hu := hCol x m u hma
    have hv := hCol x m v hma
    exact hu.trans ((h hxl).trans hv.symm)

/-- The full pointed pair-type comparison through any cut l <= m < a
is similarly invariant. The repeated first coordinate m has
identical singleton type on both sides in either graph. -/
theorem middleColumn_sameTwoPointed_iff
    (H K : Ordered3Graph Nat)
    (a m l u v : Nat)
    (hCol : MiddleColumnAgreementBelow H K a)
    (hma : m < a) (hlm : l ≤ m) :
    H.SameTwoTypeBelow l m u m v ↔
      K.SameTwoTypeBelow l m u m v := by
  have hOne : H.SameOneTypeBelow l u v ↔
      K.SameOneTypeBelow l u v :=
    middleColumn_sameOneType_iff H K a l u v hCol
      (hlm.trans hma.le)
  have hAux : H.SameAuxTypeBelow l m u m v ↔
      K.SameAuxTypeBelow l m u m v :=
    middleColumn_sameAuxPointed_iff H K a m l u v hCol hma
  constructor
  · rintro ⟨_,hu,hp⟩
    refine ⟨?_,hOne.mp hu,hAux.mp hp⟩
    intro x y hxy hyl
    rfl
  · rintro ⟨_,hu,hp⟩
    refine ⟨?_,hOne.mpr hu,hAux.mpr hp⟩
    intro x y hxy hyl
    rfl

/-- The capped singleton meet of two vertices, for which all
relevant cuts are <= min(u,v) <= a, is determined by those
earlier middle-coordinate columns. -/
theorem middleColumn_oneMeetLevel_eq
    (H K : Ordered3Graph Nat)
    (a u v : Nat)
    (hCol : MiddleColumnAgreementBelow H K a)
    (hua : min u v ≤ a) :
    H.oneMeetLevel u v = K.oneMeetLevel u v := by
  classical
  apply le_antisymm
  · have hBound := H.oneMeetLevel_le_min u v
    have hAgreement : K.SameOneTypeBelow
        (H.oneMeetLevel u v) u v :=
      (middleColumn_sameOneType_iff H K a
        (H.oneMeetLevel u v) u v hCol
        (hBound.trans hua)).mp (H.oneMeetLevel_agree u v)
    exact Nat.le_findGreatest hBound hAgreement
  · have hBound := K.oneMeetLevel_le_min u v
    have hAgreement : H.SameOneTypeBelow
        (K.oneMeetLevel u v) u v :=
      (middleColumn_sameOneType_iff H K a
        (K.oneMeetLevel u v) u v hCol
        (hBound.trans hua)).mpr (K.oneMeetLevel_agree u v)
    exact Nat.le_findGreatest hBound hAgreement

/-- The literal capped full meet of (m,u) and (m,v) is
determined by columns below a whenever m < a. -/
theorem middleColumn_twoMeetLevel_pointed_eq
    (H K : Ordered3Graph Nat)
    (a m u v : Nat)
    (hCol : MiddleColumnAgreementBelow H K a)
    (hma : m < a) :
    H.twoMeetLevel m u m v =
      K.twoMeetLevel m u m v := by
  classical
  apply le_antisymm
  · have hBound := H.twoMeetLevel_le_min m u m v
    have hBoundM : H.twoMeetLevel m u m v ≤ m := by
      simpa only [min_self] using hBound
    have hAgreement : K.SameTwoTypeBelow
        (H.twoMeetLevel m u m v) m u m v :=
      (middleColumn_sameTwoPointed_iff H K a m
        (H.twoMeetLevel m u m v) u v hCol hma hBoundM).mp
        (H.twoMeetLevel_agree m u m v)
    exact Nat.le_findGreatest hBound hAgreement
  · have hBound := K.twoMeetLevel_le_min m u m v
    have hBoundM : K.twoMeetLevel m u m v ≤ m := by
      simpa only [min_self] using hBound
    have hAgreement : H.SameTwoTypeBelow
        (K.twoMeetLevel m u m v) m u m v :=
      (middleColumn_sameTwoPointed_iff H K a m
        (K.twoMeetLevel m u m v) u v hCol hma hBoundM).mpr
        (K.twoMeetLevel_agree m u m v)
    exact Nat.le_findGreatest hBound hAgreement

/-- The full manuscript lexicographic relation LexEarlier H a b
is unchanged under ANY modifications to edges whose middle
coordinate is a or greater. No role or diary hypotheses are
used, and the current pair's own marker bits may change. -/
theorem middleColumn_lexEarlier_iff
    (H K : Ordered3Graph Nat)
    (a b : Nat) (hab : a < b)
    (hCol : MiddleColumnAgreementBelow H K a) :
    LexEarlier H a b ↔ LexEarlier K a b := by
  classical
  have hMeet : H.oneMeetLevel a b = K.oneMeetLevel a b :=
    middleColumn_oneMeetLevel_eq H K a a b hCol
      (by simp [min_eq_left hab.le])
  let m := H.oneMeetLevel a b
  have hmBound : m ≤ a :=
    (H.oneMeetLevel_le_min a b).trans (min_le_left _ _)
  by_cases hma : m < a
  · have hTwo : H.twoMeetLevel m a m b =
        K.twoMeetLevel m a m b :=
      middleColumn_twoMeetLevel_pointed_eq H K a m a b hCol hma
    have hEdge :
        H.edge (H.twoMeetLevel m a m b) m b ↔
        K.edge (K.twoMeetLevel m a m b) m b := by
      rw [hTwo]
      exact hCol (K.twoMeetLevel m a m b) m b hma
    have hCore :
        ((a < b ∧ m = a) ∨
          (m < min a b ∧
           H.edge (H.twoMeetLevel m a m b) m b)) ↔
        ((a < b ∧ m = a) ∨
          (m < min a b ∧
           K.edge (K.twoMeetLevel m a m b) m b)) :=
      or_congr Iff.rfl (and_congr Iff.rfl hEdge)
    simpa only [LexEarlier, ← hMeet] using hCore
  · have hCap : m = a := by omega
    have hCapK : K.oneMeetLevel a b = a := hMeet.symm.trans hCap
    have hLeft : LexEarlier H a b := Or.inl ⟨hab,hCap⟩
    have hRight : LexEarlier K a b := Or.inl ⟨hab,hCapK⟩
    exact ⟨fun _ => hRight,fun _ => hLeft⟩

end DiaryLeafPriority
end ThreeUniformDiaries
