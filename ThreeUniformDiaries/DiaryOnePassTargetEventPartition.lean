import ThreeUniformDiaries.DiaryOnePassSelectedEventRealization

/-!
# Actual one-pass event edges determine precisely the source children

This is the first genuinely TWO-WAY local partition theorem expressed
in the new target hypergraph, rather than in synthetic source codes.

Within a single original m-type parent:
* when m is a leaf, equality of the complete vector of ACTUAL
  one-split event edges (0,e,f(u)) in block m is equivalent to
  equality of the source singleton terminal/normal germ at m;
* when m is not a 2-split, equality of all ACTUAL pair-event edges
  (e,f(a),f(b)) in block m is equivalent to equality of the original
  capped/normal full ordered-pair germ.

Every selected source germ is represented by an event (prior module),
and each such target edge is reflected exactly (prior module).
The argument includes terminal children and makes no S1/S2
assumptions. It is the local partition step towards the main
two-way original-cut transport induction. The latter is NOT
claimed here, nor are target V/E/S or flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Local singleton child partition expressed in the actual TARGET
relation, not just as finite source class bits. -/
theorem source_oneGerm_eq_iff_target_event_bit_agreement
    (H : Ordered3Graph Nat) (m u v : Nat)
    (hm : IsLeaf H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hparent : oneCode H m u = oneCode H m v) :
    (∀ (i : Fin (onePassBlock H m).length) (g : OneGermSpace m),
      onePassEventAt H m i = BlockEvent.singleton m g →
      ((onePassRawTarget H).edge 0
          (onePassEventPosition H m i) (onePassOldImage H u) ↔
       (onePassRawTarget H).edge 0
          (onePassEventPosition H m i) (onePassOldImage H v))) ↔
    oneGermCode H m u = oneGermCode H m v := by
  classical
  constructor
  · intro htests
    apply (source_oneGerm_eq_iff_selected_bits H m u v
      hu hv hmu hmv hparent).mp
    intro c hc
    obtain ⟨i,hi⟩ := selected_oneGerm_occurs_as_event H m hm c hc
    have hU : (onePassRawTarget H).edge 0
          (onePassEventPosition H m i) (onePassOldImage H u) ↔
        oneGermCode H m u = c := by
      simpa only [hu, hmu, true_and] using
        (onePassRawTarget_singleton_incidence_iff H m u i c hi)
    have hV : (onePassRawTarget H).edge 0
          (onePassEventPosition H m i) (onePassOldImage H v) ↔
        oneGermCode H m v = c := by
      simpa only [hv, hmv, true_and] using
        (onePassRawTarget_singleton_incidence_iff H m v i c hi)
    exact hU.symm.trans ((htests i c hi).trans hV)
  · intro heq i g hi
    have hU : (onePassRawTarget H).edge 0
          (onePassEventPosition H m i) (onePassOldImage H u) ↔
        oneGermCode H m u = g := by
      simpa only [hu, hmu, true_and] using
        (onePassRawTarget_singleton_incidence_iff H m u i g hi)
    have hV : (onePassRawTarget H).edge 0
          (onePassEventPosition H m i) (onePassOldImage H v) ↔
        oneGermCode H m v = g := by
      simpa only [hv, hmv, true_and] using
        (onePassRawTarget_singleton_incidence_iff H m v i g hi)
    have hCodes : (oneGermCode H m u = g) ↔
        (oneGermCode H m v = g) := by
      rw [heq]
    exact hU.trans (hCodes.trans hV.symm)

/-- Local full pair child partition expressed as equality of
ACTUAL pair-event edges in one block. Terminal caps are included. -/
theorem source_twoGerm_eq_iff_target_event_bit_agreement
    (H : Ordered3Graph Nat) (m a b c d : Nat)
    (hm3 : 3 ≤ m) (hNotTwo : ¬ IsTwoSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m ≤ a) (hab : a < b)
    (hmc : m ≤ c) (hcd : c < d)
    (hparent : twoCode H m a b = twoCode H m c d) :
    (∀ (i : Fin (onePassBlock H m).length) (g : TwoGermSpace m),
      onePassEventAt H m i = BlockEvent.pair m g →
      ((onePassRawTarget H).edge
          (onePassEventPosition H m i)
          (onePassOldImage H a) (onePassOldImage H b) ↔
       (onePassRawTarget H).edge
          (onePassEventPosition H m i)
          (onePassOldImage H c) (onePassOldImage H d))) ↔
    twoGermCode H m a b = twoGermCode H m c d := by
  classical
  constructor
  · intro htests
    apply (source_twoGerm_eq_iff_selected_bits H m a b c d
      ha hb hc hd hma hab hmc hcd hparent).mp
    intro g hg
    obtain ⟨i,hi⟩ :=
      selected_twoGerm_occurs_as_event H m hm3 hNotTwo g hg
    have hAB : (onePassRawTarget H).edge
          (onePassEventPosition H m i)
          (onePassOldImage H a) (onePassOldImage H b) ↔
        twoGermCode H m a b = g := by
      simpa only [ha, hb, hma, hab, true_and] using
        (onePassRawTarget_pair_incidence_iff H m a b i g hi)
    have hCD : (onePassRawTarget H).edge
          (onePassEventPosition H m i)
          (onePassOldImage H c) (onePassOldImage H d) ↔
        twoGermCode H m c d = g := by
      simpa only [hc, hd, hmc, hcd, true_and] using
        (onePassRawTarget_pair_incidence_iff H m c d i g hi)
    exact hAB.symm.trans ((htests i g hi).trans hCD)
  · intro heq i g hi
    have hAB : (onePassRawTarget H).edge
          (onePassEventPosition H m i)
          (onePassOldImage H a) (onePassOldImage H b) ↔
        twoGermCode H m a b = g := by
      simpa only [ha, hb, hma, hab, true_and] using
        (onePassRawTarget_pair_incidence_iff H m a b i g hi)
    have hCD : (onePassRawTarget H).edge
          (onePassEventPosition H m i)
          (onePassOldImage H c) (onePassOldImage H d) ↔
        twoGermCode H m c d = g := by
      simpa only [hc, hd, hmc, hcd, true_and] using
        (onePassRawTarget_pair_incidence_iff H m c d i g hi)
    have hCodes : (twoGermCode H m a b = g) ↔
        (twoGermCode H m c d = g) := by
      rw [heq]
    exact hAB.trans (hCodes.trans hCD.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
