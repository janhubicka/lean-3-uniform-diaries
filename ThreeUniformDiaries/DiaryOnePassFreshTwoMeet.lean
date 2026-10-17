import ThreeUniformDiaries.DiaryOnePassDefaultPrePairEventAgreement
import ThreeUniformDiaries.DiaryOnePassFreshWitnessCones
import ThreeUniformDiaries.DiaryOnePassOldSplitWitnessTransport

/-!
# Exact fresh 2-split meets at their actual event positions

The selected/default pair-germ pre-event theorem proves that two
ordered leaf pairs (u,v) and (a,b) representing a selected full pair
germ g and its distinct realised default h have exactly the same
full target two-type BEFORE the selected event e.

The incidence iff theorem makes (e,f(u),f(v)) a positive target
edge and (e,f(a),f(b)) a nonedge. Thus their full two-types first
disagree on the auxiliary test at e, and their actual target
twoMeetLevel equals e numerically.

Both pairs lie strictly after e in the concrete target. This is the
new V2 meet witness, not just an abstract separation of finite
germ labels. The complete V2 witness axiom follows by exhausting
the old and new 2-split vertex cases.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Real selected and default sibling pair germs meet at EXACTLY
the actual fresh event vertex that selects the positive germ. -/
theorem onePass_freshTwo_selected_default_meet_exact
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g h : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g)
    (hdef : twoDefaultGerm H m g.1 = some h)
    (hparent : h.1 = g.1)
    (u v a b : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hmu : m ≤ u) (hma : m ≤ a)
    (huv : u < v) (hab : a < b)
    (huvg : twoGermCode H m u v = g)
    (habh : twoGermCode H m a b = h)
    (hneq : h ≠ g) :
    (onePassRawTarget H).twoMeetLevel
      (onePassOldImage H u) (onePassOldImage H v)
      (onePassOldImage H a) (onePassOldImage H b) =
      onePassEventPosition H m i := by
  classical
  let e := onePassEventPosition H m i
  have hBefore :
      (onePassRawTarget H).SameTwoTypeBelow e
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b) :=
    onePass_freshTwo_default_agree_before P m i g h
      hget hdef hparent u v a b
      hu hv ha hb hmu hma huv hab huvg habh
  have hPositive : (onePassRawTarget H).edge
      e (onePassOldImage H u) (onePassOldImage H v) :=
    (onePassRawTarget_pair_incidence_iff H m u v i g hget).mpr
      ⟨hu,hv,hmu,huv,huvg⟩
  have hNegative :
      ¬ (onePassRawTarget H).edge
        e (onePassOldImage H a) (onePassOldImage H b) := by
    intro he
    have hcode :=
      ((onePassRawTarget_pair_incidence_iff
        H m a b i g hget).mp he).2.2.2.2
    exact hneq (habh.symm.trans hcode)
  have hNotNext :
      ¬ (onePassRawTarget H).SameTwoTypeBelow
        (e + 1)
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b) := by
    intro hNext
    have hBit : ((onePassRawTarget H).edge
        e (onePassOldImage H u) (onePassOldImage H v) ↔
        (onePassRawTarget H).edge
        e (onePassOldImage H a) (onePassOldImage H b)) :=
      hNext.2.2 (by omega)
    exact hNegative (hBit.mp hPositive)
  have huAfter : e < onePassOldImage H u :=
    onePassEventPosition_lt_oldImage H m u i hmu
  have haAfter : e < onePassOldImage H a :=
    onePassEventPosition_lt_oldImage H m a i hma
  have hBound : e ≤ min
      (onePassOldImage H u) (onePassOldImage H a) := by
    omega
  have hLower : e ≤
      (onePassRawTarget H).twoMeetLevel
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b) :=
    Nat.le_findGreatest hBound hBefore
  have hUpper :
      (onePassRawTarget H).twoMeetLevel
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b) <
        e + 1 := by
    by_contra hBad
    have hGe : e + 1 ≤
        (onePassRawTarget H).twoMeetLevel
          (onePassOldImage H u) (onePassOldImage H v)
          (onePassOldImage H a) (onePassOldImage H b) := by
      omega
    have hAgree :=
      (onePassRawTarget H).twoMeetLevel_agree
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b)
    have hNext :
        (onePassRawTarget H).SameTwoTypeBelow (e + 1)
          (onePassOldImage H u) (onePassOldImage H v)
          (onePassOldImage H a) (onePassOldImage H b) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact hAgree.1 hxy (by omega)
      · intro x y hxy hy
        exact hAgree.2.1 hxy (by omega)
      · intro x hx
        exact hAgree.2.2 (by omega)
    exact hNotNext hNext
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
