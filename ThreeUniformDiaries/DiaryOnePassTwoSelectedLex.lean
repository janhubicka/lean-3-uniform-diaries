import ThreeUniformDiaries.DiaryOnePassFreshLexOrientation
import ThreeUniformDiaries.DiaryOnePassDefaultPreEventAgreement
import ThreeUniformDiaries.DiaryOnePassFullBlockNodup

/-!
# Lexicographic order of two genuinely selected singleton children

The previously verified fresh singleton orientation compares a
selected child with its *default*. To control V3 for two selected
children, let i<j be their actual event indices in the SAME source
block B_m and suppose their realised singleton parent types agree.

All earlier target events k<i are different from BOTH selected
labels, by injectivity of the concrete block enumeration. Pair
events have no singleton tests. Therefore the source children
agree in their target singleton types up to the earlier event i.
At i the first child is positive, the second negative, giving
the exact target oneMeetLevel=i. The genuine target LexEarlier
comparison is the RIGHT zero-coordinate bit, so the child chosen
at the earlier event is lexicographically LATER.

No source or target S1/S2, no target V3, no abstract event bits.
This is a local step toward full preservation of source leaf lex.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Two selected sibling singleton germs at distinct positions
i<j have identical ACTUAL singleton types before event i. -/
theorem onePass_twoSelected_oneType_agree_before
    (P : RolePrediary H) (m : Nat)
    (i j : Fin (onePassBlock H m).length)
    (g h : OneGermSpace m)
    (hgeti : onePassEventAt H m i = BlockEvent.singleton m g)
    (hgetj : onePassEventAt H m j = BlockEvent.singleton m h)
    (hij : i.val < j.val)
    (hparent : g.1 = h.1)
    (u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hug : oneGermCode H m u = g)
    (hvh : oneGermCode H m v = h) :
    (onePassRawTarget H).SameOneTypeBelow
      (onePassEventPosition H m i)
      (onePassOldImage H u) (onePassOldImage H v) := by
  classical
  have hSourceParent : oneCode H m u = oneCode H m v := calc
    oneCode H m u = g.1 := congrArg Prod.fst hug
    _ = h.1 := hparent
    _ = oneCode H m v := (congrArg Prod.fst hvh).symm
  have hm3 := onePassEvent_cut_ge_three H m i
  have hBase :=
    (onePass_global_oneType_transport P m u v hm3 hu hv hmu hmv).mp
      ((oneCode_eq_iff_sameOneType H m u v).mp hSourceParent)
  have hStart := (onePassEventPosition_interval H m i).1
  apply ((onePassRawTarget H).sameOneTypeBelow_interval_iff
    (onePassBefore H m)
    (onePassEventPosition H m i)
    (onePassOldImage H u) (onePassOldImage H v)
    hStart).mpr
  refine ⟨hBase, ?_⟩
  intro a b hab hstart hbend
  have hbBeforeOld : b < onePassOldImage H m :=
    lt_trans hbend (onePassEventPosition_interval H m i).2
  obtain ⟨k,hk⟩ :=
    onePassBlock_event_at_every_interval_position
      H m b hstart hbBeforeOld
  have hki : k.val < i.val := by
    dsimp [onePassEventPosition] at hk hbend
    omega
  have hkj : k.val < j.val := by omega
  rw [← hk]
  rcases onePass_event_label_at_own_cut H m k with
      ⟨t,hPair⟩ | ⟨t,hOne⟩
  · exact iff_of_false
      (onePassRawTarget_freshTwo_no_one_test P m k t hPair
        a (onePassOldImage H u))
      (onePassRawTarget_freshTwo_no_one_test P m k t hPair
        a (onePassOldImage H v))
  · by_cases ha0 : a = 0
    · subst a
      have htneqg : t ≠ g := by
        intro htg
        have hSame :
            onePassEventAt H m k = onePassEventAt H m i := by
          rw [hOne,hgeti,htg]
        exact (onePassEventAt_ne_of_lt H m i k hki) hSame
      have htneqh : t ≠ h := by
        intro hth
        have hSame :
            onePassEventAt H m k = onePassEventAt H m j := by
          rw [hOne,hgetj,hth]
        exact (onePassEventAt_ne_of_lt H m j k hkj) hSame
      have hNotU :
          ¬ (onePassRawTarget H).edge 0
             (onePassEventPosition H m k) (onePassOldImage H u) := by
        intro hed
        have hclass :=
          ((onePassRawTarget_singleton_incidence_iff
            H m u k t hOne).mp hed).2.2
        exact htneqg (hug.symm.trans hclass).symm
      have hNotV :
          ¬ (onePassRawTarget H).edge 0
             (onePassEventPosition H m k) (onePassOldImage H v) := by
        intro hed
        have hclass :=
          ((onePassRawTarget_singleton_incidence_iff
            H m v k t hOne).mp hed).2.2
        exact htneqh (hvh.symm.trans hclass).symm
      exact iff_of_false hNotU hNotV
    · have hRole :=
        onePassRawTarget_fresh_oneSplit H m k t hOne
      exact iff_of_false
        (onePassRawTarget_oneSplit_no_nonzero_middle P
          (onePassEventPosition H m k) a
          (onePassOldImage H u) hRole ha0)
        (onePassRawTarget_oneSplit_no_nonzero_middle P
          (onePassEventPosition H m k) a
          (onePassOldImage H v) hRole ha0)

/-- For two genuinely selected same-parent sibling germs,
the EARLIER selected event exactly realises their full singleton
meet, and its positive class is lexicographically later. -/
theorem onePass_twoSelected_lex_orientation
    (P : RolePrediary H) (m : Nat)
    (i j : Fin (onePassBlock H m).length)
    (g h : OneGermSpace m)
    (hgeti : onePassEventAt H m i = BlockEvent.singleton m g)
    (hgetj : onePassEventAt H m j = BlockEvent.singleton m h)
    (hij : i.val < j.val)
    (hparent : g.1 = h.1)
    (u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hug : oneGermCode H m u = g)
    (hvh : oneGermCode H m v = h) :
    (onePassRawTarget H).oneMeetLevel
       (onePassOldImage H u) (onePassOldImage H v) =
         onePassEventPosition H m i ∧
    ¬ LexEarlier (onePassRawTarget H)
       (onePassOldImage H u) (onePassOldImage H v) ∧
      LexEarlier (onePassRawTarget H)
       (onePassOldImage H v) (onePassOldImage H u) := by
  classical
  let G := onePassRawTarget H
  let e := onePassEventPosition H m i
  let a := onePassOldImage H u
  let b := onePassOldImage H v
  have hBefore : G.SameOneTypeBelow e a b :=
    onePass_twoSelected_oneType_agree_before P m i j
      g h hgeti hgetj hij hparent u v hu hv hmu hmv hug hvh
  have hPositive : G.edge 0 e a :=
    (onePassRawTarget_singleton_incidence_iff
      H m u i g hgeti).mpr ⟨hu,hmu,hug⟩
  have hDifferent : g ≠ h := by
    intro hEq
    have hSame : onePassEventAt H m i =
        onePassEventAt H m j := by
      rw [hgeti,hgetj,hEq]
    have heq := (onePassEventAt_injective H m) hSame
    have hv := congrArg Fin.val heq
    omega
  have hNegative : ¬ G.edge 0 e b := by
    intro he
    have hcode :=
      ((onePassRawTarget_singleton_incidence_iff
        H m v i g hgeti).mp he).2.2
    exact hDifferent (hcode.symm.trans hvh)
  have hNotNext : ¬ G.SameOneTypeBelow (e + 1) a b := by
    intro hNext
    have hBit : (G.edge 0 e a ↔ G.edge 0 e b) :=
      hNext (a := 0) (b := e)
        (by have he3 := onePassEventPosition_ge_three H m i; omega)
        (by omega)
    exact hNegative (hBit.mp hPositive)
  have haAfter : e < a :=
    onePassEventPosition_lt_oldImage H m u i hmu
  have hbAfter : e < b :=
    onePassEventPosition_lt_oldImage H m v i hmv
  have hBound : e ≤ min a b := by omega
  have hLower : e ≤ G.oneMeetLevel a b :=
    Nat.le_findGreatest hBound hBefore
  have hUpper : G.oneMeetLevel a b < e + 1 := by
    by_contra hBad
    have hGe : e + 1 ≤ G.oneMeetLevel a b := by omega
    have hAgree := G.oneMeetLevel_agree a b
    have hNext : G.SameOneTypeBelow (e + 1) a b := by
      intro x y hxy hy
      exact hAgree hxy (by omega)
    exact hNotNext hNext
  have hMeet : G.oneMeetLevel a b = e := by omega
  have hDiff : ¬ (G.edge 0 e a ↔ G.edge 0 e b) := by
    intro hEq
    exact hNegative (hEq.mp hPositive)
  have hLexAB : LexEarlier G a b ↔ G.edge 0 e b :=
    lexEarlier_iff_zero_middle_right_of_bit_disagreement
      G e a b haAfter hbAfter hMeet hDiff
  have hMeetRev : G.oneMeetLevel b a = e := by
    rw [G.oneMeetLevel_comm]
    exact hMeet
  have hDiffRev : ¬ (G.edge 0 e b ↔ G.edge 0 e a) := by
    intro hEq
    exact hNegative (hEq.mpr hPositive)
  have hLexBA : LexEarlier G b a ↔ G.edge 0 e a :=
    lexEarlier_iff_zero_middle_right_of_bit_disagreement
      G e b a hbAfter haAfter hMeetRev hDiffRev
  exact ⟨hMeet, fun h => hNegative (hLexAB.mp h),
    hLexBA.mpr hPositive⟩

end DiaryLeafPriority
end ThreeUniformDiaries
