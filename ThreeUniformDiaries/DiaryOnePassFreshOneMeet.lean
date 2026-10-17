import ThreeUniformDiaries.DiaryOnePassDefaultPreEventAgreement

/-!
# Exact new singleton split meets at their concrete event positions

At an inserted singleton event e selecting original germ g and with
same-parent default germ h, choose original leaves u,v representing
those two germs.

The previously checked before-event theorem proves genuine target
singleton type agreement below e (including ALL earlier selected
events, not merely the original parent code).
The target event edge is positive on u and negative on v because
their source germ labels differ. Consequently target singleton
types disagree at e+1. Since both target leaves lie strictly
after e, the actual target oneMeetLevel is EXACTLY e.

This is the local numerical meet-witness theorem for fresh
1-splits, conditional only on REALISED representatives of g,h.
A separate existence wrapper will produce such representatives
from the default-child witness theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- The actual target one-meet of two source leaves representing
a selected singleton child and its real default sibling is
exactly the NEW EVENT index (not merely at most the index). -/
theorem onePass_freshOne_selected_default_meet_exact
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g h : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g)
    (hdef : oneDefaultGerm H m g.1 = some h)
    (hparent : h.1 = g.1)
    (u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hug : oneGermCode H m u = g)
    (hvh : oneGermCode H m v = h)
    (hneq : h ≠ g) :
    (onePassRawTarget H).oneMeetLevel
      (onePassOldImage H u) (onePassOldImage H v) =
        onePassEventPosition H m i := by
  classical
  let e := onePassEventPosition H m i
  have hBefore :
      (onePassRawTarget H).SameOneTypeBelow e
        (onePassOldImage H u) (onePassOldImage H v) :=
    onePass_freshOne_default_agree_before P m i g h
      hget hdef hparent u v hu hv hmu hmv hug hvh
  have hPositive : (onePassRawTarget H).edge
      0 e (onePassOldImage H u) :=
    (onePassRawTarget_singleton_incidence_iff
      H m u i g hget).mpr ⟨hu,hmu,hug⟩
  have hNegative :
      ¬ (onePassRawTarget H).edge
        0 e (onePassOldImage H v) := by
    intro he
    have hvIn :=
      ((onePassRawTarget_singleton_incidence_iff
        H m v i g hget).mp he).2.2
    exact hneq (hvh.symm.trans hvIn)
  have he3 : 3 ≤ e := onePassEventPosition_ge_three H m i
  have hNotNext :
      ¬ (onePassRawTarget H).SameOneTypeBelow (e + 1)
        (onePassOldImage H u) (onePassOldImage H v) := by
    intro hNext
    have hBit : ((onePassRawTarget H).edge 0 e
        (onePassOldImage H u) ↔
        (onePassRawTarget H).edge 0 e
          (onePassOldImage H v)) :=
      hNext (a := 0) (b := e) (by omega) (by omega)
    exact hNegative (hBit.mp hPositive)
  have huAfter : e < onePassOldImage H u :=
    onePassEventPosition_lt_oldImage H m u i hmu
  have hvAfter : e < onePassOldImage H v :=
    onePassEventPosition_lt_oldImage H m v i hmv
  have hBound : e ≤ min
      (onePassOldImage H u) (onePassOldImage H v) := by
    omega
  have hLower : e ≤
      (onePassRawTarget H).oneMeetLevel
        (onePassOldImage H u) (onePassOldImage H v) :=
    Nat.le_findGreatest hBound hBefore
  have hUpper :
      (onePassRawTarget H).oneMeetLevel
        (onePassOldImage H u) (onePassOldImage H v) < e + 1 := by
    by_contra hBad
    have hGe : e + 1 ≤
        (onePassRawTarget H).oneMeetLevel
          (onePassOldImage H u) (onePassOldImage H v) := by
      omega
    have hAgree :=
      (onePassRawTarget H).oneMeetLevel_agree
        (onePassOldImage H u) (onePassOldImage H v)
    have hNext :
        (onePassRawTarget H).SameOneTypeBelow (e + 1)
          (onePassOldImage H u) (onePassOldImage H v) := by
      intro a b hab hb
      exact hAgree hab (by omega)
    exact hNotNext hNext
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
