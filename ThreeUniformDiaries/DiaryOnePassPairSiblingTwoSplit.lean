import ThreeUniformDiaries.DiaryOnePassTwoSelectedPairMeet
import ThreeUniformDiaries.DiaryOnePassDefaultWitnesses
import ThreeUniformDiaries.DiaryOnePassSelectedEventRealization

/-!
# Distinct realised full-pair sibling germs meet at a fresh 2-split

This is the complete local pair analogue of the verified S1
singleton-sibling analysis. Fix an original cut m>=3 that is NOT a
2-split. For any two ordered source leaf pairs with first coordinates
at/above m, equal genuine parent full two-type and distinct actual
normal/terminal germ codes, the exact target twoMeet is a fresh
2-split inserted before the old source vertex m.

One genuine pair-germ child per realised parent is the unselected
default; every other child has an actual pair event. Both selected
children meet at their earlier event (#639), and a selected/default
pair meets at the selected event (#605). All possibilities are
exhausted without assuming source S1/S2 or target diary axioms.

A reusable general pair-swap lemma is recorded as well; it requires
no ordering or diary hypotheses.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- The literal capped full ordered-pair meet is symmetric when
the two pairs are exchanged, without any diary hypotheses. -/
theorem onePass_twoMeetLevel_swapPairs
    (G : Ordered3Graph Nat) (u v a b : Nat) :
    G.twoMeetLevel u v a b = G.twoMeetLevel a b u v := by
  classical
  apply Nat.le_antisymm
  · have h := G.twoMeetLevel_agree u v a b
    have hSwap : G.SameTwoTypeBelow
        (G.twoMeetLevel u v a b) a b u v := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact (h.1 hxy hy).symm
      · intro x y hxy hy
        exact (h.2.1 hxy hy).symm
      · intro x hx
        exact (h.2.2 hx).symm
    have hBound : G.twoMeetLevel u v a b ≤ min a u := by
      simpa [min_comm] using (G.twoMeetLevel_le_min u v a b)
    exact Nat.le_findGreatest hBound hSwap
  · have h := G.twoMeetLevel_agree a b u v
    have hSwap : G.SameTwoTypeBelow
        (G.twoMeetLevel a b u v) u v a b := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact (h.1 hxy hy).symm
      · intro x y hxy hy
        exact (h.2.1 hxy hy).symm
      · intro x hx
        exact (h.2.2 hx).symm
    have hBound : G.twoMeetLevel a b u v ≤ min u a := by
      simpa [min_comm] using (G.twoMeetLevel_le_min a b u v)
    exact Nat.le_findGreatest hBound hSwap

/-- A genuinely realised pair germ that is NOT selected must be
exactly the unique chosen full pair-germ default of its parent. -/
theorem onePass_realTwoGerm_not_selected_is_default
    (H : Ordered3Graph Nat) (m : Nat)
    (g : TwoGermSpace m)
    (hReal : g ∈ realisedTwoGerms H m)
    (hNot : g ∉ selectedTwoGerms H m) :
    twoDefaultGerm H m g.1 = some g := by
  classical
  by_contra hBad
  apply hNot
  exact (selectedTwoGerm_mem_iff H m g).mpr
    ⟨hReal, fun heq => hBad heq.symm⟩

/-- At a source cut m that permits pair events, two distinct TRUE
realised same-parent full pair germs have target full two-meet at
an ACTUAL fresh 2-split vertex. -/
theorem onePass_pairBlock_sibling_meet_twoSplit
    (P : RolePrediary H) (m u v a b : Nat)
    (hm3 : 3 ≤ m) (hNotTwo : ¬ IsTwoSplit H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hmu : m ≤ u) (hma : m ≤ a)
    (huv : u < v) (hab : a < b)
    (hParent : twoCode H m u v = twoCode H m a b)
    (hDifferent : twoGermCode H m u v ≠
      twoGermCode H m a b) :
    IsTwoSplit (onePassRawTarget H)
      ((onePassRawTarget H).twoMeetLevel
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b)) := by
  classical
  let G := onePassRawTarget H
  let g := twoGermCode H m u v
  let h := twoGermCode H m a b
  have hParentG : g.1 = h.1 := hParent
  have hNe : g ≠ h := hDifferent
  have hgReal : g ∈ realisedTwoGerms H m := by
    simp only [realisedTwoGerms, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨u,v,hu,hv,hmu,huv,rfl⟩
  have hhReal : h ∈ realisedTwoGerms H m := by
    simp only [realisedTwoGerms, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨a,b,ha,hb,hma,hab,rfl⟩
  by_cases hgSelected : g ∈ selectedTwoGerms H m
  · obtain ⟨i,hi⟩ :=
      selected_twoGerm_occurs_as_event
        H m hm3 hNotTwo g hgSelected
    by_cases hhSelected : h ∈ selectedTwoGerms H m
    · obtain ⟨j,hj⟩ :=
        selected_twoGerm_occurs_as_event
          H m hm3 hNotTwo h hhSelected
      have hIndexNe : i ≠ j := by
        intro heq
        subst j
        have hLabel : BlockEvent.pair m g =
            BlockEvent.pair m h := hi.symm.trans hj
        injection hLabel with _ hGerm
        exact hNe hGerm
      by_cases hij : i.val < j.val
      · have hMeet :=
          onePass_twoSelected_pair_meet_exact
            P m i j g h hi hj hij hParentG
            u v a b hu hv ha hb hmu hma huv hab rfl rfl
        rw [hMeet]
        exact onePassRawTarget_fresh_twoSplit H m i g hi
      · have hji : j.val < i.val := by
          have hVal : i.val ≠ j.val := by
            intro heq
            exact hIndexNe (Fin.ext heq)
          omega
        have hMeetRev :=
          onePass_twoSelected_pair_meet_exact
            P m j i h g hj hi hji hParentG.symm
            a b u v ha hb hu hv hma hmu hab huv rfl rfl
        have hMeet : G.twoMeetLevel
            (onePassOldImage H u) (onePassOldImage H v)
            (onePassOldImage H a) (onePassOldImage H b) =
            onePassEventPosition H m j := by
          calc
            G.twoMeetLevel
                (onePassOldImage H u) (onePassOldImage H v)
                (onePassOldImage H a) (onePassOldImage H b) =
              G.twoMeetLevel
                (onePassOldImage H a) (onePassOldImage H b)
                (onePassOldImage H u) (onePassOldImage H v) :=
                  onePass_twoMeetLevel_swapPairs G _ _ _ _
            _ = onePassEventPosition H m j := hMeetRev
        rw [hMeet]
        exact onePassRawTarget_fresh_twoSplit H m j h hj
    · have hDefault : twoDefaultGerm H m h.1 = some h :=
        onePass_realTwoGerm_not_selected_is_default
          H m h hhReal hhSelected
      have hDefaultAtG : twoDefaultGerm H m g.1 = some h := by
        rw [hParentG]
        exact hDefault
      have hMeet :=
        onePass_freshTwo_selected_default_meet_exact
          P m i g h hi hDefaultAtG hParentG.symm
          u v a b hu hv ha hb hmu hma huv hab rfl rfl hNe.symm
      rw [hMeet]
      exact onePassRawTarget_fresh_twoSplit H m i g hi
  · have hDefault : twoDefaultGerm H m g.1 = some g :=
      onePass_realTwoGerm_not_selected_is_default
        H m g hgReal hgSelected
    have hhSelected : h ∈ selectedTwoGerms H m := by
      apply (selectedTwoGerm_mem_iff H m h).mpr
      refine ⟨hhReal, ?_⟩
      intro hEqDef
      have hOtherDefault : twoDefaultGerm H m h.1 = some g := by
        rw [← hParentG]
        exact hDefault
      have hEq : some h = some g := hEqDef.trans hOtherDefault
      exact hNe (Option.some.inj hEq).symm
    obtain ⟨j,hj⟩ :=
      selected_twoGerm_occurs_as_event
        H m hm3 hNotTwo h hhSelected
    have hDefaultAtH : twoDefaultGerm H m h.1 = some g := by
      rw [← hParentG]
      exact hDefault
    have hMeetRev :=
      onePass_freshTwo_selected_default_meet_exact
        P m j h g hj hDefaultAtH hParentG
        a b u v ha hb hu hv hma hmu hab huv rfl rfl hNe
    have hMeet : G.twoMeetLevel
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b) =
        onePassEventPosition H m j := by
      calc
        G.twoMeetLevel
            (onePassOldImage H u) (onePassOldImage H v)
            (onePassOldImage H a) (onePassOldImage H b) =
          G.twoMeetLevel
            (onePassOldImage H a) (onePassOldImage H b)
            (onePassOldImage H u) (onePassOldImage H v) :=
              onePass_twoMeetLevel_swapPairs G _ _ _ _
        _ = onePassEventPosition H m j := hMeetRev
    rw [hMeet]
    exact onePassRawTarget_fresh_twoSplit H m j h hj

end DiaryLeafPriority
end ThreeUniformDiaries
