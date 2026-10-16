import ThreeUniformDiaries.DiaryOnePassBlockCutIntervals
import ThreeUniformDiaries.DiaryOnePassEventTestCensus
import ThreeUniformDiaries.DiaryOnePassTargetEventPartition

/-!
# Actual block type-refinement partitions in source germ language

The exact target interval formulas enumerate every test inside one
finite event block. Target E shows that singleton-type tests inside
B_m occur ONLY at its 1-split events with first coordinate 0, while
auxiliary ordered-pair tests occur ONLY at its 2-split events.

Moreover, the verified exact event-edge reflection and realization
lemmas identify all of those target event bits with the original
selected germ children. Therefore, within a fixed source parent:

* for an original LEAF m, singleton agreement after the block
  equals agreement before the block PLUS equality of original
  singleton germ children (normal or terminal);
* for an original cut m not already a 2-split, auxiliary pair
  agreement after the block equals agreement before the block
  PLUS equality of original full ordered-pair germ children.

This is a genuine target type-agreement iff theorem, not a synthetic
event-code statement or an assumed inductive hypothesis. It is the
local block layer of the global original-cut induction.

The original vertex step, the global across-block induction,
protected mixed meets and target V1--V3/S1--S2 remain separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Exact SINGLETON type refinement across the whole actual B_m
when source m is a LEAF, restricted to two original source leaves
in the same original m-singleton parent. -/
theorem onePassBlock_oneType_refinement_iff
    {H : Ordered3Graph Nat} (P : RolePrediary H)
    (m u v : Nat)
    (hm : IsLeaf H m)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hparent : oneCode H m u = oneCode H m v) :
    (onePassRawTarget H).SameOneTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H u) (onePassOldImage H v) ↔
      (onePassRawTarget H).SameOneTypeBelow
        (onePassBefore H m)
        (onePassOldImage H u) (onePassOldImage H v) ∧
      oneGermCode H m u = oneGermCode H m v := by
  have hEvents :=
    onePassBlock_all_one_tests_iff_singleton_event_bits P m
      (onePassOldImage H u) (onePassOldImage H v)
  have hChildren :=
    source_oneGerm_eq_iff_target_event_bit_agreement H m u v
      hm hu hv hmu hmv hparent
  rw [onePassBlock_oneType_interval_iff H m
    (onePassOldImage H u) (onePassOldImage H v)]
  constructor
  · rintro ⟨hBase,hTests⟩
    exact ⟨hBase,hChildren.mp (hEvents.mp hTests)⟩
  · rintro ⟨hBase,hGerm⟩
    exact ⟨hBase,hEvents.mpr (hChildren.mpr hGerm)⟩

/-- Exact AUXILIARY full-pair type refinement across the whole
actual B_m when original m is NOT a 2-split, including a terminal
pair germ whose first member is the original leaf m. -/
theorem onePassBlock_auxType_refinement_iff
    {H : Ordered3Graph Nat} (P : RolePrediary H)
    (m a b c d : Nat)
    (hm3 : 3 ≤ m) (hNotTwo : ¬ IsTwoSplit H m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hma : m ≤ a) (hab : a < b)
    (hmc : m ≤ c) (hcd : c < d)
    (hparent : twoCode H m a b = twoCode H m c d) :
    (onePassRawTarget H).SameAuxTypeBelow
        (onePassOldImage H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) ↔
      (onePassRawTarget H).SameAuxTypeBelow
        (onePassBefore H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) ∧
      twoGermCode H m a b = twoGermCode H m c d := by
  have hEvents :=
    onePassBlock_all_aux_tests_iff_pair_event_bits P m
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d)
  have hChildren :=
    source_twoGerm_eq_iff_target_event_bit_agreement
      H m a b c d hm3 hNotTwo
      ha hb hc hd hma hab hmc hcd hparent
  rw [onePassBlock_auxType_interval_iff H m
    (onePassOldImage H a) (onePassOldImage H b)
    (onePassOldImage H c) (onePassOldImage H d)]
  constructor
  · rintro ⟨hBase,hTests⟩
    exact ⟨hBase,hChildren.mp (hEvents.mp hTests)⟩
  · rintro ⟨hBase,hGerm⟩
    exact ⟨hBase,hEvents.mpr (hChildren.mpr hGerm)⟩

end DiaryLeafPriority
end ThreeUniformDiaries
