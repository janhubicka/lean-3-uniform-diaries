import ThreeUniformDiaries.DiaryOnePassBlockGermTransport
import ThreeUniformDiaries.DiaryOnePassSourceGermSuccessors

/-!
# Full pair-type transport through an ORIGINAL leaf's event block

For two ordered source leaf pairs P=(a,b) and Q=(c,d) of the same
full type below an original LEAF cut m, the actual target event block
B_m simultaneously inserts auxiliary pair-germ events and
singleton-germ events.

The target full two-type after B_m consists of its two singleton
coordinates and its auxiliary pair coordinate. Each coordinate
is exactly separated by its own genuine selected-event classes.
The source full pair germ is the complete successor-cut source
two-type, and therefore determines both singleton successor types
as well.

Consequently target full pair-type agreement after the COMPLETE
B_m is equivalent to target agreement before B_m together with
source full pair-type agreement below m+1.

This is the actual target edge-relation statement, with real
normal/terminal germs, under V/E only. It does not claim the
original leaf vertex's subsequent aux column is redundant or
provide the full across-original-cuts induction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- If two ordered source leaf pairs share their original full
m-parent at a source LEAF level m, their concrete target full
two-type after the entire B_m is exactly their before-block type
together with the original source successor full pair type. -/
theorem onePass_leafBlock_twoType_refinement_iff
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsLeaf H m)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m ≤ a) (hmc : m ≤ c)
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
  have hmb : m ≤ b := hma.trans hab.le
  have hmd : m ≤ d := hmc.trans hcd.le
  have hNotTwo : ¬ IsTwoSplit H m := by
    intro ht
    exact hm.2.2 ht.2.2
  have hp0 : oneCode H m a = oneCode H m c :=
    (oneCode_eq_iff_sameOneType H m a c).mpr hParent.1
  have hp1 : oneCode H m b = oneCode H m d :=
    (oneCode_eq_iff_sameOneType H m b d).mpr hParent.2.1
  have hp2 : twoCode H m a b = twoCode H m c d :=
    (twoCode_eq_iff_sameTwoType H m a b c d).mpr hParent
  have hOne0 :=
    onePassBlock_oneType_refinement_iff P m a c
      hm ha hc hma hmc hp0
  have hOne1 :=
    onePassBlock_oneType_refinement_iff P m b d
      hm hb hd hmb hmd hp1
  have hPair :=
    onePassBlock_auxType_refinement_iff P m a b c d
      hm.1 hNotTwo ha hb hc hd hma hab hmc hcd hp2
  have hGermPair :=
    twoGerm_eq_iff_nextTwoType_of_source_leaf
      P m a b c d hm ha hb hc hd hma hab hmc hcd
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
    obtain ⟨hBefore0, _⟩ := hOne0.mp hAfter0
    obtain ⟨hBefore1, _⟩ := hOne1.mp hAfter1
    obtain ⟨hBeforeAux, hPairGerm⟩ := hPair.mp hAfterAux
    exact ⟨⟨hBefore0, hBefore1, hBeforeAux⟩,
      hGermPair.mp hPairGerm⟩
  · rintro ⟨⟨hBefore0, hBefore1, hBeforeAux⟩, hSourceNext⟩
    have hOneGerm0 :=
      (oneGerm_eq_iff_nextOneType_of_source_leaf
        P m a c hm ha hc hma hmc).mpr hSourceNext.1
    have hOneGerm1 :=
      (oneGerm_eq_iff_nextOneType_of_source_leaf
        P m b d hm hb hd hmb hmd).mpr hSourceNext.2.1
    have hPairGerm := hGermPair.mpr hSourceNext
    exact ⟨hOne0.mpr ⟨hBefore0, hOneGerm0⟩,
      hOne1.mpr ⟨hBefore1, hOneGerm1⟩,
      hPair.mpr ⟨hBeforeAux, hPairGerm⟩⟩

end DiaryLeafPriority
end ThreeUniformDiaries
