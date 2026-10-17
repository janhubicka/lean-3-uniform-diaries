import ThreeUniformDiaries.DiaryOnePassPairEventOrder
import ThreeUniformDiaries.DiaryOnePassDefaultWitnesses
import ThreeUniformDiaries.DiaryOnePassBlockCutIntervals
import ThreeUniformDiaries.DiaryOnePassGlobalTwoTypeTransport
import ThreeUniformDiaries.DiaryOnePassFullBlockNodup
import ThreeUniformDiaries.DiaryOnePassEventReflection

/-!
# Source selected/default pair germs agree before their actual event

For a selected full pair germ g at original m, let h be its realised
default sibling in the SAME original full two-type parent. Let (u,v)
and (a,b) be ordered source leaf pairs realising those two germs.

They have the same source full m-type, hence the verified global full
two-type transport yields equality of their ACTUAL target full pair
types at the start of B_m.

Every earlier event in B_m is a pair event, by the checked scheduler
order. Pair events cannot contribute singleton middle-column tests.
An earlier pair event tests some OTHER selected child k, distinct
from the designated g by block label uniqueness, and distinct from
the default h because h is omitted from the selected list. Thus
both source pairs have negative incidence at every earlier event.

It follows that their full target two-types agree through the
ACTUAL event vertex e, before E(e,f(u),f(v)) distinguishes them.

This is the difficult pre-event component of a genuine fresh V2
meet witness. The meet-level equality at e is a separate lemma.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Every actual pair event label comes from the selected full
pair-germ Finset of the same original source cut m. -/
theorem onePassEventAt_pair_selected
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g) :
    g ∈ selectedTwoGerms H m := by
  classical
  have hm3 : ¬ m < 3 := by
    have h := onePassEvent_cut_ge_three H m i
    omega
  have hNotTwo : ¬ IsTwoSplit H m :=
    onePass_pair_event_source_not_twoSplit H m i g hget
  have hmem : BlockEvent.pair m g ∈ onePassBlock H m := by
    apply (List.mem_iff_get).mpr
    exact ⟨i, hget⟩
  by_cases hLeaf : IsLeaf H m
  · have hparts : BlockEvent.pair m g ∈
      ((selectedTwoGerms H m).toList.map (BlockEvent.pair m)) ++
      ((sortOneGermsDescending m
        (selectedOneGerms H m).toList).map
        (BlockEvent.singleton m)) := by
      simpa [onePassBlock, hm3, hNotTwo, hLeaf] using hmem
    rcases List.mem_append.mp hparts with hpair | hone
    · obtain ⟨k,hk,heq⟩ := List.mem_map.mp hpair
      have hkg : k = g := by
        cases heq
        rfl
      subst k
      exact Finset.mem_toList.mp hk
    · obtain ⟨k,hk,heq⟩ := List.mem_map.mp hone
      cases heq
  · have hparts : BlockEvent.pair m g ∈
      ((selectedTwoGerms H m).toList.map (BlockEvent.pair m)) := by
      simpa [onePassBlock, hm3, hNotTwo, hLeaf] using hmem
    obtain ⟨k,hk,heq⟩ := List.mem_map.mp hparts
    have hkg : k = g := by
      cases heq
      rfl
    subst k
    exact Finset.mem_toList.mp hk

/-- Selected/default source pairs have precisely the same actual
full target two-type below their selected pair-event position.
No earlier event in the same original block distinguishes them. -/
theorem onePass_freshTwo_default_agree_before
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
    (habh : twoGermCode H m a b = h) :
    (onePassRawTarget H).SameTwoTypeBelow
       (onePassEventPosition H m i)
       (onePassOldImage H u) (onePassOldImage H v)
       (onePassOldImage H a) (onePassOldImage H b) := by
  classical
  have hSourceParent : twoCode H m u v = twoCode H m a b := calc
    twoCode H m u v = g.1 := congrArg Prod.fst huvg
    _ = h.1 := hparent.symm
    _ = twoCode H m a b := (congrArg Prod.fst habh).symm
  have hm3 : 3 ≤ m := onePassEvent_cut_ge_three H m i
  have hBase :
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b) :=
    (onePass_global_twoType_transport P m u v a b
      hm3 hu hv ha hb huv hab hmu hma).mp
      ((twoCode_eq_iff_sameTwoType H m u v a b).mp hSourceParent)
  have hStart := (onePassEventPosition_interval H m i).1
  apply ((onePassRawTarget H).sameTwoTypeBelow_interval_iff
     (onePassBefore H m)
     (onePassEventPosition H m i)
     (onePassOldImage H u) (onePassOldImage H v)
     (onePassOldImage H a) (onePassOldImage H b)
     hStart).mpr
  refine ⟨hBase, ?_, ?_, ?_⟩
  · intro x y hxy hstart hyBefore
    have hyOld : y < onePassOldImage H m :=
      lt_trans hyBefore (onePassEventPosition_interval H m i).2
    obtain ⟨j,hj⟩ :=
      onePassBlock_event_at_every_interval_position H m y hstart hyOld
    have hji : j.val < i.val := by
      dsimp [onePassEventPosition] at hj hyBefore
      omega
    rw [← hj]
    obtain ⟨k,hPair⟩ :=
      onePass_pair_event_before_singletons H m i j g hget hji
    exact iff_of_false
      (onePassRawTarget_freshTwo_no_one_test P m j k hPair
        x (onePassOldImage H u))
      (onePassRawTarget_freshTwo_no_one_test P m j k hPair
        x (onePassOldImage H a))
  · intro x y hxy hstart hyBefore
    have hyOld : y < onePassOldImage H m :=
      lt_trans hyBefore (onePassEventPosition_interval H m i).2
    obtain ⟨j,hj⟩ :=
      onePassBlock_event_at_every_interval_position H m y hstart hyOld
    have hji : j.val < i.val := by
      dsimp [onePassEventPosition] at hj hyBefore
      omega
    rw [← hj]
    obtain ⟨k,hPair⟩ :=
      onePass_pair_event_before_singletons H m i j g hget hji
    exact iff_of_false
      (onePassRawTarget_freshTwo_no_one_test P m j k hPair
        x (onePassOldImage H v))
      (onePassRawTarget_freshTwo_no_one_test P m j k hPair
        x (onePassOldImage H b))
  · intro x hstart hxBefore
    have hxOld : x < onePassOldImage H m :=
      lt_trans hxBefore (onePassEventPosition_interval H m i).2
    obtain ⟨j,hj⟩ :=
      onePassBlock_event_at_every_interval_position H m x hstart hxOld
    have hji : j.val < i.val := by
      dsimp [onePassEventPosition] at hj hxBefore
      omega
    rw [← hj]
    obtain ⟨k,hPair⟩ :=
      onePass_pair_event_before_singletons H m i j g hget hji
    have hkselected : k ∈ selectedTwoGerms H m :=
      onePassEventAt_pair_selected H m j k hPair
    have hkneqg : k ≠ g := by
      intro hkg
      have hSame :
          onePassEventAt H m j = onePassEventAt H m i := by
        rw [hPair,hget,hkg]
      exact (onePassEventAt_ne_of_lt H m i j hji) hSame
    have hkneqh : k ≠ h := by
      intro hkh
      subst k
      have hsel :=
        ((selectedTwoGerm_mem_iff H m h).mp hkselected).2
      have hDefault :
          twoDefaultGerm H m h.1 = some h := by
        rw [hparent]
        exact hdef
      exact hsel hDefault.symm
    have hNotUV :
        ¬ (onePassRawTarget H).edge
           (onePassEventPosition H m j)
           (onePassOldImage H u) (onePassOldImage H v) := by
      intro he
      have hcode :=
        ((onePassRawTarget_pair_incidence_iff
          H m u v j k hPair).mp he).2.2.2.2
      exact hkneqg (huvg.symm.trans hcode).symm
    have hNotAB :
        ¬ (onePassRawTarget H).edge
           (onePassEventPosition H m j)
           (onePassOldImage H a) (onePassOldImage H b) := by
      intro he
      have hcode :=
        ((onePassRawTarget_pair_incidence_iff
          H m a b j k hPair).mp he).2.2.2.2
      exact hkneqh (habh.symm.trans hcode).symm
    exact iff_of_false hNotUV hNotAB

end DiaryLeafPriority
end ThreeUniformDiaries
