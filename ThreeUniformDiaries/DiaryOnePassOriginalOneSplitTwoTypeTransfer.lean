import ThreeUniformDiaries.DiaryOnePassBlockGermTransport
import ThreeUniformDiaries.DiaryOnePassNonLeafSingletonBlocks
import ThreeUniformDiaries.DiaryOnePassSourceGermSuccessors
import ThreeUniformDiaries.DiaryOnePassOriginalSplitTransfer

/-!
# Full ordered-pair transport at an ORIGINAL 1-split

An old 1-split m may have new PAIR events in B_m, but the static
construction inserts no singleton events there. Those pair events
split precisely the normal full pair-type germs of the original
parent at m. These germs are exactly the full source pair types
through m+1.

Therefore full pair-type equality after the complete B_m is exactly
equality beforehand plus the original successor full pair type.

At the original 1-split vertex f(m) itself, singleton tests add the
original (0,m,u) coordinate bits and no auxiliary test is possible
because target E forbids a 1-split as first vertex of any edge.
All those singleton bits are already decided by the source next
full pair type; f(m) introduces no further distinction.

Together these give the complete conditional original-1-split step
of the global two-type transport induction. No S1/S2 assumptions.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- The full pair-type changes at the event block before an
original 1-split are exactly the SOURCE next full pair-type
refinement, even though this block has NO singleton events. -/
theorem onePass_oneSplitBlock_twoType_refinement_iff
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m < a) (hmc : m < c)
    (hab : a < b) (hcd : c < d)
    (hParent : H.SameTwoTypeBelow m a b c d) :
    (onePassRawTarget H).SameTwoTypeBelow
      (onePassOldImage H m)
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) ↔
    (onePassRawTarget H).SameTwoTypeBelow
      (onePassBefore H m)
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) ∧
    H.SameTwoTypeBelow (m + 1) a b c d := by
  have hNotLeaf : ¬ IsLeaf H m := by
    intro h
    exact h.2.1 hm.2.1
  have hNotTwo : ¬ IsTwoSplit H m := by
    intro h
    exact hm.2.2 h.2.2
  have hpCode : twoCode H m a b = twoCode H m c d :=
    (twoCode_eq_iff_sameTwoType H m a b c d).mpr hParent
  have hNoOne0 :=
    onePassBlock_oneType_unchanged_of_not_leaf P m
      (onePassOldImage H a) (onePassOldImage H c) hNotLeaf
  have hNoOne1 :=
    onePassBlock_oneType_unchanged_of_not_leaf P m
      (onePassOldImage H b) (onePassOldImage H d) hNotLeaf
  have hAux :=
    onePassBlock_auxType_refinement_iff P m a b c d
      hm.1 hNotTwo ha hb hc hd hma.le hab hmc.le hcd hpCode
  have hNormal :=
    twoGerm_eq_iff_normal H m a b c d
      (by omega : a ≠ m) (by omega : c ≠ m)
  change
    ((onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H a) (onePassOldImage H c) ∧
     (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H b) (onePassOldImage H d) ∧
     (onePassRawTarget H).SameAuxTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)) ↔
    (((onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m)
        (onePassOldImage H a) (onePassOldImage H c) ∧
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m)
        (onePassOldImage H b) (onePassOldImage H d) ∧
      (onePassRawTarget H).SameAuxTypeBelow
        (onePassBefore H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)) ∧
     H.SameTwoTypeBelow (m + 1) a b c d)
  constructor
  · rintro ⟨hAfter0, hAfter1, hAfterAux⟩
    obtain ⟨hBeforeAux, hGerm⟩ := hAux.mp hAfterAux
    exact ⟨⟨hNoOne0.mp hAfter0,
       hNoOne1.mp hAfter1, hBeforeAux⟩,
      (hNormal.mp hGerm).2⟩
  · rintro ⟨⟨hBefore0, hBefore1, hBeforeAux⟩, hSourceNext⟩
    have hGerm := hNormal.mpr ⟨hParent, hSourceNext⟩
    exact ⟨hNoOne0.mpr hBefore0,
      hNoOne1.mpr hBefore1,
      hAux.mpr ⟨hBeforeAux, hGerm⟩⟩

/-- Passing the old 1-split f(m) cannot further refine pairs
that already agree in full SOURCE type through m+1. -/
theorem onePass_oldOneSplit_twoType_extends_of_nextSource
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsOneSplit H m)
    (hSource : H.SameTwoTypeBelow (m + 1) a b c d)
    (hBefore : (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)) :
    (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m + 1)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  have h3 : 3 ≤ m := hm.1
  have hBit0 : (H.edge 0 m a ↔ H.edge 0 m c) :=
    hSource.1 (by omega) (by omega)
  have hBit1 : (H.edge 0 m b ↔ H.edge 0 m d) :=
    hSource.2.1 (by omega) (by omega)
  have hOne0 :=
    (onePass_original_oneSplit_nextOneCut P m a c hm).mpr
      ⟨hBefore.1, hBit0⟩
  have hOne1 :=
    (onePass_original_oneSplit_nextOneCut P m b d hm).mpr
      ⟨hBefore.2.1, hBit1⟩
  have hTargetRole : IsOneSplit (onePassRawTarget H)
      (onePassOldImage H m) :=
    (onePassRawTarget_old_oneSplit_iff H m).mpr hm
  have hAux : (onePassRawTarget H).SameAuxTypeBelow
      (onePassOldImage H m + 1)
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) := by
    intro x hx
    by_cases hOld : x < onePassOldImage H m
    · exact hBefore.2.2 hOld
    · have hEq : x = onePassOldImage H m := by omega
      subst x
      exact iff_of_false
        (onePassRawTarget_oneSplit_no_first P
          (onePassOldImage H m)
          (onePassOldImage H a) (onePassOldImage H b)
          hTargetRole)
        (onePassRawTarget_oneSplit_no_first P
          (onePassOldImage H m)
          (onePassOldImage H c) (onePassOldImage H d)
          hTargetRole)
  exact ⟨hOne0, hOne1, hAux⟩

/-- The complete conditional full pair-type original 1-split step:
source/target cut equality BEFORE B_m gives equality immediately
after the old 1-split's image, i.e. at the start of B_(m+1). -/
theorem onePass_original_oneSplit_twoType_transfer
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsOneSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m < a) (hmc : m < c)
    (hab : a < b) (hcd : c < d)
    (hPrevious : H.SameTwoTypeBelow m a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassBefore H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)) :
    H.SameTwoTypeBelow (m + 1) a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m + 1)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  constructor
  · intro hSourceNext
    have hParent : H.SameTwoTypeBelow m a b c d := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact hSourceNext.1 hxy (by omega)
      · intro x y hxy hy
        exact hSourceNext.2.1 hxy (by omega)
      · intro x hx
        exact hSourceNext.2.2 (by omega)
    have hBlock :=
      onePass_oneSplitBlock_twoType_refinement_iff
        P m a b c d hm ha hb hc hd hma hmc hab hcd hParent
    have hTargetBefore :=
      hBlock.mpr ⟨hPrevious.mp hParent, hSourceNext⟩
    exact onePass_oldOneSplit_twoType_extends_of_nextSource
      P m a b c d hm hSourceNext hTargetBefore
  · intro hTargetNext
    have hTargetOld :
        (onePassRawTarget H).SameTwoTypeBelow
          (onePassOldImage H m)
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact hTargetNext.1 hxy (by omega)
      · intro x y hxy hy
        exact hTargetNext.2.1 hxy (by omega)
      · intro x hx
        exact hTargetNext.2.2 (by omega)
    have hStart :
        (onePassRawTarget H).SameTwoTypeBelow
          (onePassBefore H m)
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) :=
      ((onePassBlock_twoType_interval_iff H m
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)).mp
        hTargetOld).1
    have hParent : H.SameTwoTypeBelow m a b c d :=
      hPrevious.mpr hStart
    exact ((onePass_oneSplitBlock_twoType_refinement_iff
      P m a b c d hm ha hb hc hd hma hmc hab hcd
      hParent).mp hTargetOld).2

end DiaryLeafPriority
end ThreeUniformDiaries
