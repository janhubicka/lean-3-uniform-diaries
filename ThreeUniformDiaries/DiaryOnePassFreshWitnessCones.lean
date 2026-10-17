import ThreeUniformDiaries.DiaryOnePassDefaultWitnesses
import ThreeUniformDiaries.DiaryOnePassSelectedEventRealization
import ThreeUniformDiaries.DiaryOnePassEventReflection

/-!
# Real positive and negative source witnesses for every new split

Every selected source germ g inserted by the actual finite-block
scheduler has a realised default child h with the same old parent
type but a genuinely different germ signature. This is the precise
source-side witness pair needed to show the new event's meet level.

Here we turn these Finset facts into positive and negative edges of
the ACTUAL target relation for an actual new event position. The
two witnesses in each arity are source leaves or ordered source leaf
pairs, agree in the original full parent type, and have OPPOSITE
incidence at that new event.

Their actual target singleton and pair-type agreement BEFORE the event is
not asserted here; proving that requires uniqueness of earlier
event labels and the global block cut transport machinery.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Actual realisation of any selected singleton germ by an old leaf. -/
theorem selectedOneGerm_source_leaf
    (H : Ordered3Graph Nat) (m : Nat)
    (g : OneGermSpace m) (hg : g ∈ selectedOneGerms H m) :
    ∃ u : Nat, IsLeaf H u ∧ m ≤ u ∧ oneGermCode H m u = g := by
  classical
  have hreal : g ∈ realisedOneGerms H m :=
    ((selectedOneGerm_mem_iff H m g).mp hg).1
  simpa only [realisedOneGerms, Finset.mem_filter,
    Finset.mem_univ, true_and] using hreal

/-- Every realised singleton germ has an actual source leaf. -/
theorem realisedOneGerm_source_leaf
    (H : Ordered3Graph Nat) (m : Nat)
    (g : OneGermSpace m) (hg : g ∈ realisedOneGerms H m) :
    ∃ u : Nat, IsLeaf H u ∧ m ≤ u ∧ oneGermCode H m u = g := by
  classical
  simpa only [realisedOneGerms, Finset.mem_filter,
    Finset.mem_univ, true_and] using hg

/-- Every selected singleton child yields a real 1-event with
positive and negative target leaf images in the SAME source
singleton parent. The negative image lies in the default child. -/
theorem selectedOneGerm_actual_positive_negative
    (H : Ordered3Graph Nat) (m : Nat) (hm : IsLeaf H m)
    (g : OneGermSpace m) (hg : g ∈ selectedOneGerms H m) :
    ∃ (i : Fin (onePassBlock H m).length) (u v : Nat),
      onePassEventAt H m i = BlockEvent.singleton m g ∧
      IsLeaf H u ∧ IsLeaf H v ∧
      m ≤ u ∧ m ≤ v ∧
      oneCode H m u = oneCode H m v ∧
      (onePassRawTarget H).edge 0
        (onePassEventPosition H m i) (onePassOldImage H u) ∧
      ¬ (onePassRawTarget H).edge 0
        (onePassEventPosition H m i) (onePassOldImage H v) := by
  classical
  obtain ⟨h,hhreal,hhparent,hneq,hdef⟩ :=
    selectedOneGerm_has_distinct_default H m g hg
  obtain ⟨u,hu,hmu,hug⟩ :=
    selectedOneGerm_source_leaf H m g hg
  obtain ⟨v,hv,hmv,hvh⟩ :=
    realisedOneGerm_source_leaf H m h hhreal
  obtain ⟨i,hi⟩ :=
    selected_oneGerm_occurs_as_event H m hm g hg
  have hparent : oneCode H m u = oneCode H m v := calc
    oneCode H m u = g.1 := congrArg Prod.fst hug
    _ = h.1 := hhparent.symm
    _ = oneCode H m v := (congrArg Prod.fst hvh).symm
  have hpositive :
      (onePassRawTarget H).edge 0
        (onePassEventPosition H m i) (onePassOldImage H u) :=
    (onePassRawTarget_singleton_incidence_iff
      H m u i g hi).mpr ⟨hu,hmu,hug⟩
  have hnegative :
      ¬ (onePassRawTarget H).edge 0
        (onePassEventPosition H m i) (onePassOldImage H v) := by
    intro hed
    have hclass :=
      ((onePassRawTarget_singleton_incidence_iff
        H m v i g hi).mp hed).2.2
    exact hneq (hvh.symm.trans hclass)
  exact ⟨i,u,v,hi,hu,hv,hmu,hmv,hparent,hpositive,hnegative⟩

/-- Actual realisation of any selected full pair germ. -/
theorem selectedTwoGerm_source_pair
    (H : Ordered3Graph Nat) (m : Nat)
    (g : TwoGermSpace m) (hg : g ∈ selectedTwoGerms H m) :
    ∃ u v : Nat, IsLeaf H u ∧ IsLeaf H v ∧
      m ≤ u ∧ u < v ∧ twoGermCode H m u v = g := by
  classical
  have hreal : g ∈ realisedTwoGerms H m :=
    ((selectedTwoGerm_mem_iff H m g).mp hg).1
  simpa only [realisedTwoGerms, Finset.mem_filter,
    Finset.mem_univ, true_and] using hreal

/-- Realisation of an arbitrary actual source full pair germ. -/
theorem realisedTwoGerm_source_pair
    (H : Ordered3Graph Nat) (m : Nat)
    (g : TwoGermSpace m) (hg : g ∈ realisedTwoGerms H m) :
    ∃ u v : Nat, IsLeaf H u ∧ IsLeaf H v ∧
      m ≤ u ∧ u < v ∧ twoGermCode H m u v = g := by
  classical
  simpa only [realisedTwoGerms, Finset.mem_filter,
    Finset.mem_univ, true_and] using hg

/-- Every selected pair germ yields an ACTUAL pair event and two
realised source leaf pairs in the SAME full two-type parent,
one positive and the other negative at that event. -/
theorem selectedTwoGerm_actual_positive_negative
    (H : Ordered3Graph Nat) (m : Nat)
    (hm3 : 3 ≤ m) (hNotTwo : ¬ IsTwoSplit H m)
    (g : TwoGermSpace m) (hg : g ∈ selectedTwoGerms H m) :
    ∃ (i : Fin (onePassBlock H m).length) (u v a b : Nat),
      onePassEventAt H m i = BlockEvent.pair m g ∧
      IsLeaf H u ∧ IsLeaf H v ∧ IsLeaf H a ∧ IsLeaf H b ∧
      m ≤ u ∧ u < v ∧ m ≤ a ∧ a < b ∧
      twoCode H m u v = twoCode H m a b ∧
      (onePassRawTarget H).edge
        (onePassEventPosition H m i)
        (onePassOldImage H u) (onePassOldImage H v) ∧
      ¬ (onePassRawTarget H).edge
        (onePassEventPosition H m i)
        (onePassOldImage H a) (onePassOldImage H b) := by
  classical
  obtain ⟨h,hhreal,hhparent,hneq,hdef⟩ :=
    selectedTwoGerm_has_distinct_default H m g hg
  obtain ⟨u,v,hu,hv,hmu,huv,huvg⟩ :=
    selectedTwoGerm_source_pair H m g hg
  obtain ⟨a,b,ha,hb,hma,hab,habh⟩ :=
    realisedTwoGerm_source_pair H m h hhreal
  obtain ⟨i,hi⟩ :=
    selected_twoGerm_occurs_as_event H m hm3 hNotTwo g hg
  have hparent : twoCode H m u v = twoCode H m a b := calc
    twoCode H m u v = g.1 := congrArg Prod.fst huvg
    _ = h.1 := hhparent.symm
    _ = twoCode H m a b := (congrArg Prod.fst habh).symm
  have hpositive :
      (onePassRawTarget H).edge
        (onePassEventPosition H m i)
        (onePassOldImage H u) (onePassOldImage H v) :=
    (onePassRawTarget_pair_incidence_iff
      H m u v i g hi).mpr ⟨hu,hv,hmu,huv,huvg⟩
  have hnegative :
      ¬ (onePassRawTarget H).edge
        (onePassEventPosition H m i)
        (onePassOldImage H a) (onePassOldImage H b) := by
    intro hed
    have hclass :=
      ((onePassRawTarget_pair_incidence_iff
        H m a b i g hi).mp hed).2.2.2.2
    exact hneq (habh.symm.trans hclass)
  exact ⟨i,u,v,a,b,hi,hu,hv,ha,hb,hmu,huv,hma,hab,
    hparent,hpositive,hnegative⟩

end DiaryLeafPriority
end ThreeUniformDiaries
