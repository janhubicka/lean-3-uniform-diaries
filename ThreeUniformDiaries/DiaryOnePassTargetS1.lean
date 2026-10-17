import ThreeUniformDiaries.DiaryOnePassGlobalV3
import ThreeUniformDiaries.DiaryOnePassFreshOneMeet
import ThreeUniformDiaries.DiaryOnePassTwoSelectedLex
import ThreeUniformDiaries.DiaryOnePassOldSplitWitnessTransport
import ThreeUniformDiaries.DiaryOnePassTargetLeafCones

/-!
# Complete target S1: every two distinct leaves meet at an actual 1-split

The source pre-diary need not satisfy S1. Given distinct actual source
leaves u,v, the source first singleton meet is either a 1-split or
a leaf, as proved from source V/E alone in the global V3 development.

An original 1-split meet transports exactly to its existing target
1-split image. At an original leaf m, both original leaves have
distinct true successor/terminal germs in the same original m-parent.
If both germs are selected, the earlier of their two REAL singleton
events is their exact target one-meet. If one is unselected, it is
the REAL default and the selected child's event is their exact meet.
Every such fresh event is literally IsOneSplit in the constructed
target (not merely a synthetically labelled role).

Finally every target leaf is an image of an original leaf. Exhausting
those cases establishes the full literal RoleDiary.singleton_meets
axiom S1 without assuming source S1/S2 or target pre-diary axioms.

This does not assert S2, flip absorption, or the printed stronger
universal preservation claim.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Two distinct source singleton child germs in a genuine original
LEAF block have target one-meet at a newly inserted actual 1-split.
The source children may be terminal or normal and may be selected or
the real default. -/
theorem onePass_leafBlock_sibling_meet_oneSplit
    (P : RolePrediary H) (m u v : Nat)
    (hm : IsLeaf H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hParent : oneCode H m u = oneCode H m v)
    (hDifferent : oneGermCode H m u ≠ oneGermCode H m v) :
    IsOneSplit (onePassRawTarget H)
      ((onePassRawTarget H).oneMeetLevel
        (onePassOldImage H u) (onePassOldImage H v)) := by
  classical
  let G := onePassRawTarget H
  let g := oneGermCode H m u
  let h := oneGermCode H m v
  have hParentG : g.1 = h.1 := hParent
  have hNe : g ≠ h := hDifferent
  have hgReal : g ∈ realisedOneGerms H m := by
    simp only [realisedOneGerms, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨u, hu, hmu, rfl⟩
  have hhReal : h ∈ realisedOneGerms H m := by
    simp only [realisedOneGerms, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨v, hv, hmv, rfl⟩
  by_cases hgSelected : g ∈ selectedOneGerms H m
  · obtain ⟨i, hi⟩ :=
      selected_oneGerm_occurs_as_event H m hm g hgSelected
    by_cases hhSelected : h ∈ selectedOneGerms H m
    · obtain ⟨j, hj⟩ :=
        selected_oneGerm_occurs_as_event H m hm h hhSelected
      have hIndexNe : i ≠ j := by
        intro heq
        subst j
        have hLabel : BlockEvent.singleton m g =
            BlockEvent.singleton m h := hi.symm.trans hj
        injection hLabel with _ hGerm
        exact hNe hGerm
      by_cases hij : i.val < j.val
      · have hMeet := (onePass_twoSelected_lex_orientation
            P m i j g h hi hj hij hParentG u v
            hu hv hmu hmv rfl rfl).1
        rw [hMeet]
        exact onePassRawTarget_fresh_oneSplit H m i g hi
      · have hji : j.val < i.val := by
          have hVal : i.val ≠ j.val := by
            intro heq
            exact hIndexNe (Fin.ext heq)
          omega
        have hMeetRev := (onePass_twoSelected_lex_orientation
            P m j i h g hj hi hji hParentG.symm v u
            hv hu hmv hmu rfl rfl).1
        have hMeet : G.oneMeetLevel
            (onePassOldImage H u) (onePassOldImage H v) =
            onePassEventPosition H m j :=
          (G.oneMeetLevel_comm _ _).trans hMeetRev
        rw [hMeet]
        exact onePassRawTarget_fresh_oneSplit H m j h hj
    · have hDefault : oneDefaultGerm H m h.1 = some h :=
        onePass_realOneGerm_not_selected_is_default
          H m h hhReal hhSelected
      have hDefaultAtG : oneDefaultGerm H m g.1 = some h := by
        rw [hParentG]
        exact hDefault
      have hMeet :=
        onePass_freshOne_selected_default_meet_exact P m
          i g h hi hDefaultAtG hParentG.symm u v
          hu hv hmu hmv rfl rfl hNe.symm
      rw [hMeet]
      exact onePassRawTarget_fresh_oneSplit H m i g hi
  · have hDefault : oneDefaultGerm H m g.1 = some g :=
      onePass_realOneGerm_not_selected_is_default
        H m g hgReal hgSelected
    have hhSelected : h ∈ selectedOneGerms H m := by
      apply (selectedOneGerm_mem_iff H m h).mpr
      refine ⟨hhReal, ?_⟩
      intro hEqDef
      have hOtherDefault : oneDefaultGerm H m h.1 = some g := by
        rw [← hParentG]
        exact hDefault
      have hEq : some h = some g :=
        hEqDef.trans hOtherDefault
      exact hNe (Option.some.inj hEq).symm
    obtain ⟨j, hj⟩ :=
      selected_oneGerm_occurs_as_event H m hm h hhSelected
    have hDefaultAtH : oneDefaultGerm H m h.1 = some g := by
      rw [← hParentG]
      exact hDefault
    have hMeetRev :=
      onePass_freshOne_selected_default_meet_exact P m
        j h g hj hDefaultAtH hParentG v u
        hv hu hmv hmu rfl rfl hNe
    have hMeet : G.oneMeetLevel
        (onePassOldImage H u) (onePassOldImage H v) =
        onePassEventPosition H m j :=
      (G.oneMeetLevel_comm _ _).trans hMeetRev
    rw [hMeet]
    exact onePassRawTarget_fresh_oneSplit H m j h hj

/-- COMPLETE S1 for the actual one-pass target: the first singleton
meet of ANY two different target leaves is literally a 1-split.
Only source RolePrediary V/E hypotheses are used. -/
theorem onePassRawTarget_singleton_meets
    (P : RolePrediary H) :
    ∀ a b : Nat, IsLeaf (onePassRawTarget H) a →
      IsLeaf (onePassRawTarget H) b → a ≠ b →
      IsOneSplit (onePassRawTarget H)
        ((onePassRawTarget H).oneMeetLevel a b) := by
  intro a b ha hb hne
  obtain ⟨u, hu, hImageU⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H a).mp ha
  obtain ⟨v, hv, hImageV⟩ :=
    (onePassRawTarget_leaf_iff_oldLeaf_image H b).mp hb
  have huv : u ≠ v := by
    intro heq
    apply hne
    calc
      a = onePassOldImage H u := hImageU.symm
      _ = onePassOldImage H v := by rw [heq]
      _ = b := hImageV
  rw [← hImageU, ← hImageV]
  let m := H.oneMeetLevel u v
  have hCap : m ≤ min u v := H.oneMeetLevel_le_min u v
  have hmu : m ≤ u := hCap.trans (min_le_left _ _)
  have hmv : m ≤ v := hCap.trans (min_le_right _ _)
  rcases onePass_source_leafOneMeet_is_leaf_or_oneSplit
      P u v hu hv with hLeaf | hOne
  · have hParent : oneCode H m u = oneCode H m v :=
      (oneCode_eq_iff_sameOneType H m u v).mpr (by
        change H.SameOneTypeBelow (H.oneMeetLevel u v) u v
        exact H.oneMeetLevel_agree u v)
    have hGermNe : oneGermCode H m u ≠
        oneGermCode H m v :=
      onePass_firstOneMeet_trueGerms_distinct
        H m u v hmu hmv huv rfl
    exact onePass_leafBlock_sibling_meet_oneSplit
      P m u v hLeaf hu hv hmu hmv hParent hGermNe
  · have hmu' : m < u := by
      have hNotEq : m ≠ u := by
        intro heq
        have hSplitU : IsOneSplit H u := by
          have he : H.oneMeetLevel u v = u := heq
          simpa only [he] using hOne
        exact hu.2.1 hSplitU.2.1
      omega
    have hmv' : m < v := by omega
    have hMeetTarget := onePass_oldOneSplit_meet_exact
      P m u v hOne hu hv hmu' hmv' rfl
    rw [hMeetTarget]
    exact (onePassRawTarget_old_oneSplit_iff H m).mpr hOne

end DiaryLeafPriority
end ThreeUniformDiaries
