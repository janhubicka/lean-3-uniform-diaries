import ThreeUniformDiaries.DiaryReservedOldColourTailDichotomy
import ThreeUniformDiaries.DiaryStableGenericPairPatternColour
import ThreeUniformDiaries.DiaryRelativeMultiColourTailObstruction

/-!
# Track A: a genuine generic leaf range always has bad cofinal old-cut colours

Fix an ACTUAL old reserved diary stage f with at least TWO distinct
selected old source leaves a<b, and let m be the next true source
leaf. A complete singleton colour at the old-stage cut B remembers
the exact target E5 incidence with the fixed old target leaf pair
(f a,f b). Any genuine compatible reserved next-leaf image w must
realize the SOURCE-required bit H.edge a b m.

Thus a target vertex v with the OPPOSITE E5 bit determines a
whole COMPLETE B-colour class containing NO compatible next-leaf
image, even if the colour occurs arbitrarily far out.

When the prescribed target true-leaf range is one unordered
induced copy of the enumerated generic 3-hypergraph, the existing
verified generic finite-pattern theorem produces a SINGLE complete
B-colour with the opposite bit that recurs cofinally in BOTH
source index and target numerical position. This is an ACTUAL
cofinally inhabited but wholly BAD colour class for the fixed
old stage.

This is a necessary adversarial obstruction to deriving relative
diary unavoidability from generic vertex-colour recurrence alone.
It does not show that every cofinal colour is bad, nor that no
compatible reserved successor exists in other colours.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Noncomputable Boolean choice of the OPPOSITE of a specified
old source pair's required next-leaf E5 bit. Defined separately
so theorem statements need no implicit Decidable proposition. -/
noncomputable def oppositeOldPairE5Bit
    (H : Ordered3Graph Nat) (a b m : Nat) : Bool := by
  classical
  exact decide (¬ H.edge a b m)

/-- Wrong E5 incidence at even ONE fixed ordered old selected pair
makes the entire complete singleton colour of v impossible for
a compatible reserved next-leaf image.

This uses exact old-support fixation and edge AND nonedge reflection,
not any infinite embedding or unproved relative realization. -/
theorem ReservedDiaryStage.wrong_old_pair_E5_bit_forbids_compatible_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m a b B v : Nat}
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (hBound : f b < B)
    (hWrong : ¬ (H.edge a b m ↔ K.edge (f a) (f b) v)) :
    ∀ w : Nat, HasCompatibleReservedNextLeaf H K F f m w →
      DiaryLowerBoundColors.singletonColour K B w ≠
        DiaryLowerBoundColors.singletonColour K B v := by
  intro w hGood hEqual
  have haOld : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a ha
  have hbOld : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) b hb
  have hOrder : f a < f b := P.1.ordered a b haOld hbOld hab
  obtain ⟨g, Q, hCompat, hNew⟩ := hGood
  have haNext : a ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) a
      ((countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) ha)
  have hbNext : b ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) b
      ((countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) hb)
  have hmNext : m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m
      ((mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
        ⟨hm.1, by omega, hm⟩)
  have hbm : b < m :=
    ((mem_countableDiaryLeafPrefix_iff H m b).mp hb).2.1
  have hActual : H.edge a b m ↔ K.edge (f a) (f b) w := by
    have hStage :=
      Q.1.induced_edge a b m haNext hbNext hmNext hab hbm
    have hFixA : g a = f a := hCompat a haOld
    have hFixB : g b = f b := hCompat b hbOld
    simpa only [hFixA, hFixB, hNew] using hStage
  have hTargetBit :
      K.edge (f a) (f b) v ↔ K.edge (f a) (f b) w :=
    same_singletonColour_forces_same_old_pair_edge
      K B (f a) (f b) v w hOrder hBound hEqual.symm
  exact hWrong (hActual.trans hTargetBit.symm)

/-- Every ACTUAL reserved old stage with two selected leaves in a
genuine prescribed unordered GENERIC true-leaf range has one
COFINALLY INHABITED COMPLETE old-cut singleton colour which
admits NO compatible reserved next-leaf image.

The cofinality is simultaneous in the original generic source
index and target numeric image. The colour is fixed before all
lower bounds, and its badness is not vacuous: actual generic
leaves of this colour recur arbitrarily far out.

No assumption that any other colour is good is made. -/
theorem ReservedDiaryStage.exists_cofinal_bad_generic_next_leaf_colour
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b) :
    let B := oldStageTailCut H m f
    ∃ c : Fin B → Fin B → Bool,
      HasCofinalGenericPairPatternColour G K F B
        (fun _ _ => oppositeOldPairE5Bit H a b m) c ∧
      (∀ w : Nat, HasCompatibleReservedNextLeaf H K F f m w →
        DiaryLowerBoundColors.singletonColour K B w ≠ c) := by
  classical
  let B := oldStageTailCut H m f
  let chi : Nat → Nat → Bool :=
    fun _ _ => oppositeOldPairE5Bit H a b m
  have haOld : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a ha
  have hbOld : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) b hb
  have hOrder : f a < f b := P.1.ordered a b haOld hbOld hab
  obtain ⟨i, hi⟩ := P.1.leaf_range a haOld
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  obtain ⟨j, hj⟩ := P.1.leaf_range b hbOld
    ((mem_countableDiaryLeafPrefix_iff H m b).mp hb).2.2
  have hIJ : F i < F j := by
    simpa only [← hi, ← hj] using hOrder
  have hOldB : f b < B := by
    change f b <
      max ((countableDiaryFiniteSupport H m).sup f)
        ((countableDiaryLeafPrefix H m).sup f) + 1
    calc
      f b ≤ (countableDiaryLeafPrefix H m).sup f :=
        Finset.le_sup (f := f) hb
      _ ≤ max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) :=
        le_max_right _ _
      _ < max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) + 1 :=
        Nat.lt_succ_self _
  have hJB : F j < B := by
    simpa only [← hj] using hOldB
  obtain ⟨c, hRec⟩ :=
    exists_cofinal_generic_pair_pattern_full_colour
      G K F hFLeaf B chi
  refine ⟨c, hRec, ?_⟩
  obtain ⟨t, _htN, _htM, _htB, _htLeaf, hColour, hPair⟩ :=
    hRec 0 0
  have hOpp :
      (K.edge (f a) (f b) (F t) ↔ ¬ H.edge a b m) := by
    have h := hPair i j hIJ hJB
    rw [← hi, ← hj] at h
    simpa [chi, oppositeOldPairE5Bit, decide_eq_true_eq] using h
  have hWrong :
      ¬ (H.edge a b m ↔ K.edge (f a) (f b) (F t)) := by
    intro hActual
    have hFalse : H.edge a b m ↔ ¬ H.edge a b m :=
      hActual.trans hOpp
    tauto
  intro w hGood
  have hDifferent :=
    P.wrong_old_pair_E5_bit_forbids_compatible_colour
      hm ha hb hab hOldB hWrong w hGood
  intro hWC
  exact hDifferent (hWC.trans hColour.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
