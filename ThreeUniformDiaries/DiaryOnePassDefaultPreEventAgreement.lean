import ThreeUniformDiaries.DiaryOnePassDefaultWitnesses
import ThreeUniformDiaries.DiaryOnePassFullBlockNodup
import ThreeUniformDiaries.DiaryOnePassBlockCutIntervals
import ThreeUniformDiaries.DiaryOnePassTargetV1Coherence

/-!
# No earlier event distinguishes a selected singleton from its default

Fix an original cut m, a singleton event at position e in B_m
selecting realised source germ g, and the realised default sibling h
of the SAME old singleton parent. Fix source leaves u,v representing
g,h respectively.

Their source one-types agree through cut m, hence the verified
global original-cut transport gives target type agreement at the
beginning of B_m. At each EARLIER event of this SAME block:
* a pair event cannot appear as a singleton middle-coordinate test;
* a different singleton event tests some selected child k distinct
  from g by full block Nodup, and distinct from h because h is
  the unselected default; hence both source leaves have zero there.

Thus their ACTUAL target singleton types agree below e, before
the selected event introduces the first differing bit. This is
the missing pre-event half of the fresh V1 meet-witness argument.
The theorem asserts the exact concrete type relation, not an
artificial one-hot prefix or a diary axiom.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- An ACTUAL singleton event in B_m must test a member of the
actual finite selected singleton germs at that same original cut. -/
theorem onePassEventAt_singleton_selected
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g) :
    g ∈ selectedOneGerms H m := by
  classical
  have hLeaf := onePass_freshOne_event_source_leaf H m i g hget
  have hm3 : ¬ m < 3 := by
    have hbound := hLeaf.1
    omega
  have hNotTwo : ¬ IsTwoSplit H m := by
    intro ht
    exact hLeaf.2.2 ht.2.2
  have hmem : BlockEvent.singleton m g ∈ onePassBlock H m := by
    apply (List.mem_iff_get).mpr
    exact ⟨i, hget⟩
  have hparts : BlockEvent.singleton m g ∈
      ((selectedTwoGerms H m).toList.map (BlockEvent.pair m)) ++
      ((sortOneGermsDescending m
        (selectedOneGerms H m).toList).map
          (BlockEvent.singleton m)) := by
    simpa [onePassBlock,hm3,hNotTwo,hLeaf] using hmem
  rcases List.mem_append.mp hparts with hpair | hone
  · obtain ⟨k,hk,heq⟩ := List.mem_map.mp hpair
    cases heq
  · obtain ⟨k,hk,heq⟩ := List.mem_map.mp hone
    have hkg : k = g := by
      cases heq
      rfl
    subst k
    exact Finset.mem_toList.mp
      ((mem_sortOneGermsDescending_iff m g _).mp hk)

/-- For source leaves u,v in a selected singleton child g and
its realised default sibling h, NO earlier target event can
distinguish their one-types. The positive/negative test at e
itself is a separate exact incidence equivalence. -/
theorem onePass_freshOne_default_agree_before
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
    (hvh : oneGermCode H m v = h) :
    (onePassRawTarget H).SameOneTypeBelow
      (onePassEventPosition H m i)
      (onePassOldImage H u) (onePassOldImage H v) := by
  classical
  have hSourceParent : oneCode H m u = oneCode H m v := calc
    oneCode H m u = g.1 := congrArg Prod.fst hug
    _ = h.1 := hparent.symm
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
  obtain ⟨j,hj⟩ :=
    onePassBlock_event_at_every_interval_position
      H m b hstart hbBeforeOld
  have hji : j.val < i.val := by
    dsimp [onePassEventPosition] at hj hbend
    omega
  rw [← hj]
  rcases onePass_event_label_at_own_cut H m j with
      ⟨k,hPair⟩ | ⟨k,hOne⟩
  · exact iff_of_false
      (onePassRawTarget_freshTwo_no_one_test P m j k hPair
        a (onePassOldImage H u))
      (onePassRawTarget_freshTwo_no_one_test P m j k hPair
        a (onePassOldImage H v))
  · by_cases ha0 : a = 0
    · subst a
      have hkselected : k ∈ selectedOneGerms H m :=
        onePassEventAt_singleton_selected H m j k hOne
      have hkneqg : k ≠ g := by
        intro hkg
        have hSame :
            onePassEventAt H m j = onePassEventAt H m i := by
          rw [hOne,hget,hkg]
        exact (onePassEventAt_ne_of_lt H m i j hji) hSame
      have hkneqh : k ≠ h := by
        intro hkh
        subst k
        have hsel :=
          ((selectedOneGerm_mem_iff H m h).mp hkselected).2
        have hParentDefault :
            oneDefaultGerm H m h.1 = some h := by
          rw [hparent]
          exact hdef
        exact hsel hParentDefault.symm
      have hNotU :
          ¬ (onePassRawTarget H).edge 0
             (onePassEventPosition H m j) (onePassOldImage H u) := by
        intro hed
        have hclass :=
          ((onePassRawTarget_singleton_incidence_iff
            H m u j k hOne).mp hed).2.2
        exact hkneqg (hug.symm.trans hclass).symm
      have hNotV :
          ¬ (onePassRawTarget H).edge 0
             (onePassEventPosition H m j) (onePassOldImage H v) := by
        intro hed
        have hclass :=
          ((onePassRawTarget_singleton_incidence_iff
            H m v j k hOne).mp hed).2.2
        exact hkneqh (hvh.symm.trans hclass).symm
      exact iff_of_false hNotU hNotV
    · have hRole :=
        onePassRawTarget_fresh_oneSplit H m j k hOne
      exact iff_of_false
        (onePassRawTarget_oneSplit_no_nonzero_middle P
          (onePassEventPosition H m j) a
          (onePassOldImage H u) hRole ha0)
        (onePassRawTarget_oneSplit_no_nonzero_middle P
          (onePassEventPosition H m j) a
          (onePassOldImage H v) hRole ha0)

end DiaryLeafPriority
end ThreeUniformDiaries
