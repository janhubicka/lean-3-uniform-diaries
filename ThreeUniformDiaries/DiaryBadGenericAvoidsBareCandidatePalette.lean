import ThreeUniformDiaries.DiaryFiniteGoodOldCutCandidateColours
import ThreeUniformDiaries.DiaryGenericTargetOldE5PatternCopy
import ThreeUniformDiaries.DiaryFunctionalCandidateOldSupport

/-!
# Track C: a whole generic refinement avoids even the BARE full finite-candidate palette

English mathematical proof and adversarial scope audit:
  janhubicka/3-uniform-diaries PR #336.

For a genuine old reserved support stage with two distinct selected
earlier source leaves a<b, the finite candidate checker itself already
requires the correct old-old/new E5 bit over (a,b,m), before considering
FutureOrderReserve. The original unordered generic target F-range has
a WHOLE induced generic subcopy realizing the OPPOSITE bit on the
actual old target pair (f a,f b). Every leaf of this copy therefore
fails the BARE complete finite candidate predicate.

Taking the copy beyond the old-stage support cut, the existing exact
Track C finite-colour classification implies that every leaf's
complete mixed old-cut singleton colour lies OUTSIDE the entire
finite good candidate palette. No additional homogeneous thinning is
needed.

This obstruction fixes the old stage BEFORE selecting the bad generic
refinement. The copy is UNORDERED induced generic, not necessarily
AuxTypeRespecting. It does NOT contradict jointly chosen support/range
refinements, cofinal good colours in the original range, all-horizon
persistence or diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A BARE complete finite candidate must reflect the E5 edge AND
nonedge between any two old selected source leaves and the proposed
new source leaf. This uses the old full supported stage, the
functional candidate generator table, and its inducedness field,
with NO future-order reserve or full source RoleDiary assumption. -/
theorem ReservedDiaryStage.bare_candidate_preserves_old_pair_E5
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m a b v : Nat}
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (C : FiniteNewLeafCandidateCondition H K F m f v) :
    (H.edge a b m ↔ K.edge (f a) (f b) v) := by
  have haOld : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a ha
  have hbOld : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) b hb
  have haNext : a ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) a
      ((countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) ha)
  have hbNext : b ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) b
      ((countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) hb)
  have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1, by omega, hm⟩
  have hmNext : m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m hmSelected
  have hbm : b < m :=
    ((mem_countableDiaryLeafPrefix_iff H m b).mp hb).2.1
  have hOldMap :=
    P.1.functional_candidate_table_preserves_old_support C.functional
  have hNew :
      candidateNewLeafTableMap H K m f v m = v := by
    have hAtM := C.chosen_selected_leaf m hmSelected
    simpa [candidateLeafImage] using hAtM
  have hEdge :=
    C.induced_edge a b m haNext hbNext hmNext hab hbm
  simpa only [hOldMap a haOld, hOldMap b hbOld, hNew] using hEdge

/-- A FIXED genuine old reserved stage with two earlier true selected
leaves has arbitrarily far out WHOLE induced unordered generic
refinements of its original true-leaf target F-range which contain
NO BARE full finite candidate images. Consequently none of those
vertices' complete old-stage-cut singleton colours is in the finite
good candidate palette. No future reserve is used in this failure.

The refinement is chosen AFTER f and may fail to be
AuxTypeRespecting. No nonexistence of globally chosen coherent
diary embeddings or big Ramsey degrees is asserted. -/
theorem ReservedDiaryStage.exists_generic_subcopy_avoiding_bare_candidate_palette
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ n : Nat, IsLeaf K (F n))
    {m a b : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      ∀ n : Nat,
        M < J n ∧
        IsLeaf K (J n) ∧
        (∃ t : Nat, J n = F t) ∧
        ¬ FiniteNewLeafCandidateCondition H K F m f (J n) ∧
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (J n) ∉
          goodOldCutCandidateColours H K F f m := by
  classical
  let B : Nat := f b + 1
  let Cut : Nat := oldStageTailCut H m f
  have haOld : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a ha
  have hbOld : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) b hb
  have hOrder : f a < f b :=
    P.1.ordered a b haOld hbOld hab
  have haLeaf : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  have hbLeaf : IsLeaf H b :=
    ((mem_countableDiaryLeafPrefix_iff H m b).mp hb).2.2
  obtain ⟨i, hi⟩ := P.1.leaf_range a haOld haLeaf
  obtain ⟨j, hj⟩ := P.1.leaf_range b hbOld hbLeaf
  let chi : Nat → Nat → Bool :=
    fun _ _ => decide (¬ H.edge a b m)
  obtain ⟨J, hRange, hPattern⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
      G K F hFLeaf B (max M Cut) chi
  have hWrong (n : Nat) :
      ¬ (H.edge a b m ↔ K.edge (f a) (f b) (J n)) := by
    have hIndexOrder : F i < F j := by
      simpa only [← hi, ← hj] using hOrder
    have hIndexBound : F j < B := by
      simpa only [← hj] using (Nat.lt_succ_self (f b))
    have hTarget :
        K.edge (f a) (f b) (J n) ↔
          chi (f a) (f b) = true := by
      simpa only [hi, hj] using
        hPattern n i j hIndexOrder hIndexBound
    have hOpp :
        K.edge (f a) (f b) (J n) ↔
          ¬ H.edge a b m := by
      simpa [chi] using hTarget
    intro hCandidateBit
    have hImpossible : H.edge a b m ↔ ¬ H.edge a b m :=
      hCandidateBit.trans hOpp
    tauto
  refine ⟨J, ?_⟩
  intro n
  obtain ⟨hLarge, _hOldPairCut, hLeaf, t, hF⟩ := hRange n
  have hLate : M < J n :=
    lt_of_le_of_lt (le_max_left M Cut) hLarge
  have hAboveCut : Cut ≤ J n :=
    (le_max_right M Cut).trans hLarge.le
  have hNotCandidate :
      ¬ FiniteNewLeafCandidateCondition H K F m f (J n) := by
    intro C
    exact hWrong n
      (P.bare_candidate_preserves_old_pair_E5 hm ha hb hab C)
  have hNotGood :
      DiaryLowerBoundColors.singletonColour K Cut (J n) ∉
        goodOldCutCandidateColours H K F f m := by
    intro hGood
    have C :
        FiniteNewLeafCandidateCondition H K F m f (J n) :=
      (P.1.full_candidate_iff_good_oldCut_colour
        hm hAboveCut hLeaf ⟨t, hF⟩).mpr hGood
    exact hNotCandidate C
  exact ⟨hLate, hLeaf, ⟨t, hF⟩, hNotCandidate, hNotGood⟩

end DiaryLeafPriority
end ThreeUniformDiaries
