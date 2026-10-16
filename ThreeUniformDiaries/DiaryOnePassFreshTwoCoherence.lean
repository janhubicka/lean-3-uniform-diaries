import ThreeUniformDiaries.DiaryOnePassGlobalTwoTypeTransport
import ThreeUniformDiaries.DiaryOnePassLeafBlockTwoTypeTransport
import ThreeUniformDiaries.DiaryOnePassOriginalOneSplitTwoTypeTransfer
import ThreeUniformDiaries.DiaryOnePassEventReflection

/-!
# V2 coherence for actual fresh pair events on original leaf images

This is the genuine typed core of the target's V2 coherence axiom:
if two increasing ordered source leaf pairs are positive at the
same newly inserted pair event, then the FULL two-types of their
images agree through the cut at that event.

By exact target incidence reflection, both pairs have the SAME
selected original complete pair-germ at original level m. Hence
they have the same source parent m-full two-type, transported into
the real target at the start of B_m by the now verified global
full pair-type theorem. The common successor germ determines full
type equality after B_m via the two local original-role cases:
  * source m leaf: original normal/terminal pair-germ refinement,
  * source m 1-split: normal pair-germ refinement.
A source 2-split has no inserted pair events by construction.

The target event is strictly before the old image f(m), so full
two-type agreement after B_m restricts to agreement before e.

No target V2 witness, V3, S1/S2, flip absorption, or synthetic
event-type axiom is claimed. The separate target leaf-preimage
module converts this to the universal target V2 coherence clause.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- No actual pair event can exist before an original 2-split:
the whole B_m is empty there, including singleton events. -/
theorem onePass_pair_event_source_not_twoSplit
    (H : Ordered3Graph Nat) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g) :
    ¬ IsTwoSplit H m := by
  intro hTwo
  have hNotLeaf : ¬ IsLeaf H m := by
    intro hLeaf
    exact hLeaf.2.2 hTwo.2.2
  have hEmpty : onePassBlock H m = [] := by
    have hlt : ¬ m < 3 := by
      have hBound := hTwo.1
      omega
    simp [onePassBlock, hlt, hTwo, hNotLeaf]
  have hi : i.val < 0 := by
    simpa only [hEmpty, List.length_nil] using i.isLt
  omega

/-- ACTUAL fresh pair-event V2 coherence restricted only to
original source leaf images; no synthetic positive-pair predicate. -/
theorem onePassRawTarget_freshTwo_coherent_oldImages
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g)
    (u v a b : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (huv : u < v) (hab : a < b)
    (hUV : (onePassRawTarget H).edge
      (onePassEventPosition H m i)
      (onePassOldImage H u) (onePassOldImage H v))
    (hAB : (onePassRawTarget H).edge
      (onePassEventPosition H m i)
      (onePassOldImage H a) (onePassOldImage H b)) :
    (onePassRawTarget H).SameTwoTypeBelow
      (onePassEventPosition H m i)
      (onePassOldImage H u) (onePassOldImage H v)
      (onePassOldImage H a) (onePassOldImage H b) := by
  have hSourceUV :=
    (onePassRawTarget_pair_incidence_iff H m u v i g hget).mp hUV
  have hSourceAB :=
    (onePassRawTarget_pair_incidence_iff H m a b i g hget).mp hAB
  have hmu : m ≤ u := hSourceUV.2.2.1
  have hma : m ≤ a := hSourceAB.2.2.1
  have hGerm : twoGermCode H m u v = twoGermCode H m a b :=
    hSourceUV.2.2.2.2.trans hSourceAB.2.2.2.2.symm
  have hParentCode : twoCode H m u v = twoCode H m a b :=
    congrArg Prod.fst hGerm
  have hParent : H.SameTwoTypeBelow m u v a b :=
    (twoCode_eq_iff_sameTwoType H m u v a b).mp hParentCode
  have hm3 : 3 ≤ m := onePassEvent_cut_ge_three H m i
  have hBegin :
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b) :=
    (onePass_global_twoType_transport P m u v a b
      hm3 hu hv ha hb huv hab hmu hma).mp hParent
  have hFull :
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H u) (onePassOldImage H v)
        (onePassOldImage H a) (onePassOldImage H b) := by
    rcases P.role_valid m hm3 with hLeaf | hOne | hTwo
    · have hNext :=
        (twoGerm_eq_iff_nextTwoType_of_source_leaf
          P m u v a b hLeaf hu hv ha hb hmu huv hma hab).mp hGerm
      exact (onePass_leafBlock_twoType_refinement_iff P m
        u v a b hLeaf huv hab hu hv ha hb hmu hma hParent).mpr
        ⟨hBegin, hNext⟩
    · have hmu' : m < u := by
        have hne : m ≠ u := by
          intro heq
          subst u
          exact hu.2.1 hOne.2.1
        omega
      have hma' : m < a := by
        have hne : m ≠ a := by
          intro heq
          subst a
          exact ha.2.1 hOne.2.1
        omega
      have hNext :=
        ((twoGerm_eq_iff_normal H m u v a b
          (by omega : u ≠ m)
          (by omega : a ≠ m)).mp hGerm).2
      exact (onePass_oneSplitBlock_twoType_refinement_iff P m
        u v a b hOne hu hv ha hb hmu' hma' huv hab hParent).mpr
        ⟨hBegin, hNext⟩
    · exact False.elim
        ((onePass_pair_event_source_not_twoSplit H m i g hget) hTwo)
  have hEnd := (onePassEventPosition_interval H m i).2
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    exact hFull.1 hxy (by omega)
  · intro x y hxy hy
    exact hFull.2.1 hxy (by omega)
  · intro x hx
    exact hFull.2.2 (by omega)

end DiaryLeafPriority
end ThreeUniformDiaries
