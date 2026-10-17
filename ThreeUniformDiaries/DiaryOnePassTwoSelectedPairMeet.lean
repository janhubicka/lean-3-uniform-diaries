import ThreeUniformDiaries.DiaryOnePassDefaultPrePairEventAgreement
import ThreeUniformDiaries.DiaryOnePassFreshTwoMeet

/-!
# Exact target full-pair meet for two selected siblings

The previously verified before-event theorem compares a selected pair
germ with its genuinely realised DEFAULT sibling, ensuring agreement
of the FULL target pair types (both singleton coordinates and the
auxiliary coordinate) up to its own selected pair-event position.

For two selected source pair germs g,h of the same parent at indices
i<j, choose the common realised default k. Pair g agrees with k
below event i. Pair h agrees with k below event j, hence also below
i. By transitivity the FULL pair types of g and h agree below i.
At i the actual pair incidence is positive on g, negative on h.

Consequently the exact numerical target full twoMeetLevel of those
actual source pairs is the earlier event i, a genuine fresh 2-split.
This avoids replaying the delicate event-prefix proof, and uses no
source S1/S2 or assumed target diary axioms.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- A first positive/negative auxiliary incidence after full
two-type agreement makes the actual capped numerical twoMeetLevel
exactly the event e. No diary structure assumptions are necessary. -/
theorem twoMeet_eq_event_of_first_aux_disagreement
    (G : Ordered3Graph Nat) (e u v a b : Nat)
    (heu : e < u) (hea : e < a)
    (hBefore : G.SameTwoTypeBelow e u v a b)
    (hPos : G.edge e u v) (hNeg : ¬ G.edge e a b) :
    G.twoMeetLevel u v a b = e := by
  classical
  have hBound : e ≤ min u a := by omega
  have hLower : e ≤ G.twoMeetLevel u v a b :=
    Nat.le_findGreatest hBound hBefore
  have hUpper : G.twoMeetLevel u v a b < e + 1 := by
    by_contra hn
    have hGe : e + 1 ≤ G.twoMeetLevel u v a b := by omega
    have hAgreement := G.twoMeetLevel_agree u v a b
    have hBit : G.edge e u v ↔ G.edge e a b :=
      hAgreement.2.2 (by omega)
    exact hNeg (hBit.mp hPos)
  omega

/-- Every two distinct actual SELECTED full-pair siblings, with
source pairs witnessing their germs, have exact target full
two-type meet at the earlier concrete pair-event index. -/
theorem onePass_twoSelected_pair_meet_exact
    (P : RolePrediary H) (m : Nat)
    (i j : Fin (onePassBlock H m).length)
    (g h : TwoGermSpace m)
    (hgeti : onePassEventAt H m i = BlockEvent.pair m g)
    (hgetj : onePassEventAt H m j = BlockEvent.pair m h)
    (hij : i.val < j.val)
    (hparent : g.1 = h.1)
    (u v a b : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hmu : m ≤ u) (hma : m ≤ a)
    (huv : u < v) (hab : a < b)
    (huvg : twoGermCode H m u v = g)
    (habh : twoGermCode H m a b = h) :
    (onePassRawTarget H).twoMeetLevel
      (onePassOldImage H u) (onePassOldImage H v)
      (onePassOldImage H a) (onePassOldImage H b) =
      onePassEventPosition H m i := by
  classical
  let G := onePassRawTarget H
  let e := onePassEventPosition H m i
  have hSelected : g ∈ selectedTwoGerms H m :=
    onePassEventAt_pair_selected H m i g hgeti
  obtain ⟨k,hkReal,hkParent,_hkNe,hkDef⟩ :=
    selectedTwoGerm_has_distinct_default H m g hSelected
  obtain ⟨r,s,hr,hs,hmr,hrs,hrscode⟩ :=
    realisedTwoGerm_source_pair H m k hkReal
  have hkParentH : k.1 = h.1 := hkParent.trans hparent
  have hkDefH : twoDefaultGerm H m h.1 = some k := by
    rw [← hparent]
    exact hkDef
  have hPreG : G.SameTwoTypeBelow e
      (onePassOldImage H u) (onePassOldImage H v)
      (onePassOldImage H r) (onePassOldImage H s) :=
    onePass_freshTwo_default_agree_before
      P m i g k hgeti hkDef hkParent
        u v r s hu hv hr hs hmu hmr huv hrs huvg hrscode
  have hPreH : G.SameTwoTypeBelow
      (onePassEventPosition H m j)
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H r) (onePassOldImage H s) :=
    onePass_freshTwo_default_agree_before
      P m j h k hgetj hkDefH hkParentH
        a b r s ha hb hr hs hma hmr hab hrs habh hrscode
  have hEventEarlier : e < onePassEventPosition H m j := by
    dsimp [e, onePassEventPosition]
    omega
  have hPreHEarlier : G.SameTwoTypeBelow e
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H r) (onePassOldImage H s) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      exact hPreH.1 hxy (lt_trans hy hEventEarlier)
    · intro x y hxy hy
      exact hPreH.2.1 hxy (lt_trans hy hEventEarlier)
    · intro x hx
      exact hPreH.2.2 (lt_trans hx hEventEarlier)
  have hBefore : G.SameTwoTypeBelow e
      (onePassOldImage H u) (onePassOldImage H v)
      (onePassOldImage H a) (onePassOldImage H b) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      exact (hPreG.1 hxy hy).trans
        (hPreHEarlier.1 hxy hy).symm
    · intro x y hxy hy
      exact (hPreG.2.1 hxy hy).trans
        (hPreHEarlier.2.1 hxy hy).symm
    · intro x hx
      exact (hPreG.2.2 hx).trans (hPreHEarlier.2.2 hx).symm
  have hGermDifferent : h ≠ g := by
    intro heq
    have hLabels : onePassEventAt H m i =
        onePassEventAt H m j := by
      rw [hgeti,hgetj,heq]
    have hIndices := (onePassEventAt_injective H m) hLabels
    have hValues := congrArg Fin.val hIndices
    omega
  have hPos : G.edge e
      (onePassOldImage H u) (onePassOldImage H v) :=
    (onePassRawTarget_pair_incidence_iff H m u v i g hgeti).mpr
      ⟨hu,hv,hmu,huv,huvg⟩
  have hNeg : ¬ G.edge e
      (onePassOldImage H a) (onePassOldImage H b) := by
    intro he
    have hCode :=
      ((onePassRawTarget_pair_incidence_iff H m a b i g hgeti).mp he).2.2.2.2
    exact hGermDifferent (habh.symm.trans hCode)
  exact twoMeet_eq_event_of_first_aux_disagreement
    G e
      (onePassOldImage H u) (onePassOldImage H v)
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassEventPosition_lt_oldImage H m u i hmu)
      (onePassEventPosition_lt_oldImage H m a i hma)
      hBefore hPos hNeg

end DiaryLeafPriority
end ThreeUniformDiaries
