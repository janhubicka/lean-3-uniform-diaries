import ThreeUniformDiaries.DiaryOnePassLeafBlockTwoTypeTransport
import ThreeUniformDiaries.DiaryOnePassGlobalTwoTypeTransport
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# S2 genuine capped pair meet at an original leaf

An ordered pair meet may be capped at the common minimum of its
two first vertices. In the source pre-diary, when this minimum m
is an original LEAF and the two ordered source leaf pairs have
the same genuine successor full pair-type through m+1, the
actual one-pass event block B_m does not distinguish them.

The verified global two-type original-cut transport gives actual
target agreement at the start of B_m. The checked leaf block full
pair refinement transports the source successor-type agreement
through the whole block up to the target old-leaf image f(m).
But f(m) is exactly the new minimum of their first vertices, so
the literal target twoMeet is capped there.

This proves the difficult terminal-pair cap option of S2, with no
source S1/S2, target S2 or artificial type assumptions. The other
case, where successor germ codes differ, is handled by fresh
pair-split events in the separate local sibling theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- A source full pair meet capped at an original LEAF m remains
capped at the corresponding target old-leaf f(m), provided the
true source full pair types agree through the next source cut.
Source V/E-only; no S1/S2 are assumed. -/
theorem onePass_source_leaf_cap_twoMeet_preserved
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : IsLeaf H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hab : a < b) (hcd : c < d)
    (hma : m ≤ a) (hmc : m ≤ c)
    (hCap : m = min a c)
    (hSourceMeet : H.twoMeetLevel a b c d = m)
    (hNext : H.SameTwoTypeBelow (m + 1) a b c d) :
    (onePassRawTarget H).twoMeetLevel
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) =
    min (onePassOldImage H a) (onePassOldImage H c) := by
  classical
  let G := onePassRawTarget H
  have hParent : H.SameTwoTypeBelow m a b c d := by
    rw [← hSourceMeet]
    exact H.twoMeetLevel_agree a b c d
  have hBefore :
      G.SameTwoTypeBelow
        (onePassBefore H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) :=
    (onePass_global_twoType_transport P m a b c d
      hm.1 ha hb hc hd hab hcd hma hmc).mp hParent
  have hThrough :
      G.SameTwoTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) :=
    (onePass_leafBlock_twoType_refinement_iff P m a b c d
       hm hab hcd ha hb hc hd hma hmc hParent).mpr
      ⟨hBefore, hNext⟩
  have hMapMin :
      onePassOldImage H (min a c) =
        min (onePassOldImage H a) (onePassOldImage H c) := by
    rcases le_total a c with hac | hca
    · simp [min_eq_left hac,
        min_eq_left ((onePassOldImage_strictMono H).monotone hac)]
    · simp [min_eq_right hca,
        min_eq_right ((onePassOldImage_strictMono H).monotone hca)]
  have hCutBound : onePassOldImage H m ≤
      min (onePassOldImage H a) (onePassOldImage H c) := by
    have hleA := (onePassOldImage_strictMono H).monotone hma
    have hleC := (onePassOldImage_strictMono H).monotone hmc
    omega
  have hLower : onePassOldImage H m ≤
      G.twoMeetLevel
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) :=
    Nat.le_findGreatest hCutBound hThrough
  have hUpper : G.twoMeetLevel
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) ≤
      onePassOldImage H m := by
    have hMax := G.twoMeetLevel_le_min
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d)
    rw [← hMapMin, ← hCap] at hMax
    exact hMax
  have hEq : G.twoMeetLevel
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) =
      onePassOldImage H m := Nat.le_antisymm hUpper hLower
  calc
    G.twoMeetLevel
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) =
      onePassOldImage H m := hEq
    _ = min (onePassOldImage H a) (onePassOldImage H c) := by
      rw [← hMapMin, ← hCap]

end DiaryLeafPriority
end ThreeUniformDiaries
