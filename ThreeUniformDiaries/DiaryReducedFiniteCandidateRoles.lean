import ThreeUniformDiaries.DiaryFiniteReservedCandidateCriterion
import ThreeUniformDiaries.DiaryFutureReserveFusion
import ThreeUniformDiaries.DiaryFiniteLeafMeetRoleSupport

/-!
# Split-role checks follow from a functional ordered generator table

For a GENUINE full source and target diary, the selected leaf-meet
closure contains only the selected leaves and the actual supported
one- and two-splits. A functional finite table with strictly ordered
images and target leaves satisfies the role constraints automatically:

* an old/source one-split is a meet of two distinct selected leaves,
  so target S1 makes its forced image a genuine target one-split;
* a source two-split is a meet of two ordered selected leaf pairs.
  Target S2 says its image is marker 1, a leaf cap, or a two-split.
  The first two options contradict the table's strict order and
  fixed marker images.

Thus the extra split-role checks in the general finite candidate
criterion are redundant FOR GENUINE TARGET DIARIES. The result
does not remove the difficult induced edge/nonedge or numerical
generator-collision tests, and does not produce a target leaf.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Reduced finite test for the target leaf image v when the full
target is known to be a genuine RoleDiary and the prescribed outer
range consists entirely of target leaves. Its only geometric tests
are table functionality, strict order, and the complete induced
edge/nonedge table. -/
structure ReducedFiniteNewLeafCandidateCondition
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat) (v : Nat) : Prop where
  functional :
    FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f v)
  range : ∃ t : Nat, v = F t
  ordered : ∀ a b : Nat,
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    b ∈ countableDiaryFiniteSupport H (m + 1) →
    a < b →
    candidateNewLeafTableMap H K m f v a <
      candidateNewLeafTableMap H K m f v b
  induced_edge : ∀ a b c : Nat,
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    b ∈ countableDiaryFiniteSupport H (m + 1) →
    c ∈ countableDiaryFiniteSupport H (m + 1) →
    a < b → b < c →
    (H.edge a b c ↔
      K.edge
        (candidateNewLeafTableMap H K m f v a)
        (candidateNewLeafTableMap H K m f v b)
        (candidateNewLeafTableMap H K m f v c))

namespace ReducedFiniteNewLeafCandidateCondition

variable {H K : Ordered3Graph Nat} {F f : Nat → Nat}
variable {m v : Nat}

/-- Functionality alone fixes the target image of each selected
leaf, including the new source leaf m. -/
theorem chosen_selected_leaf
    (C : ReducedFiniteNewLeafCandidateCondition H K F m f v)
    (a : Nat) (ha : a ∈ countableDiaryLeafPrefix H (m + 1)) :
    candidateNewLeafTableMap H K m f v a =
      candidateLeafImage f m v a := by
  exact finiteGeneratorTableValue_eq_of_mem
    _ C.functional a _
    (finiteLeafGeneratorTable_leaf
      H K (countableDiaryLeafPrefix H (m + 1))
      (candidateLeafImage f m v) a ha)

/-- In a genuine target diary, the three role conditions of
the full candidate table follow from S1/S2, strict order,
and the prescribed fact that the outer range contains leaves.
This theorem does NOT assume an existing successor map. -/
theorem to_full
    (C : ReducedFiniteNewLeafCandidateCondition H K F m f v)
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t)) :
    FiniteNewLeafCandidateCondition H K F m f v := by
  classical
  let L := countableDiaryLeafPrefix H (m + 1)
  let q := candidateLeafImage f m v
  let g := candidateNewLeafTableMap H K m f v
  let T := candidateNewLeafGeneratorTable H K m f v
  have hLSource : ∀ a : Nat, a ∈ L → IsLeaf H a := by
    intro a ha
    exact ((mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha).2.2
  have hLSupport : ∀ a : Nat, a ∈ L →
      a ∈ countableDiaryFiniteSupport H (m + 1) := by
    intro a ha
    exact mem_finiteLeafMeetSupport_leaf H L a ha
  have hChosen : ∀ a : Nat, a ∈ L → g a = q a := by
    intro a ha
    exact C.chosen_selected_leaf a ha
  obtain ⟨tV,hV⟩ := C.range
  have hNewLeaf : IsLeaf K v := by
    rw [hV]
    exact hFleaf tV
  have hLTarget : ∀ a : Nat, a ∈ L → IsLeaf K (g a) := by
    intro a ha
    have hChosenA := hChosen a ha
    by_cases ham : a = m
    · subst a
      have hVal : g m = v := by
        simpa [q,candidateLeafImage] using hChosenA
      rw [hVal]
      exact hNewLeaf
    · have ha3 : 3 ≤ a :=
        ((mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha).1
      have ham1 :
          a < m + 1 :=
        ((mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha).2.1
      have haOld : a ∈ countableDiaryLeafPrefix H m :=
        (mem_countableDiaryLeafPrefix_iff H m a).mpr
          ⟨ha3,by omega,hLSource a ha⟩
      have haSupported : a ∈ countableDiaryFiniteSupport H m :=
        mem_finiteLeafMeetSupport_leaf H
          (countableDiaryLeafPrefix H m) a haOld
      have hVal : g a = f a := by
        simpa [q,candidateLeafImage,ham] using hChosenA
      rw [hVal]
      exact P.leaf_role a haSupported (hLSource a ha)
  have hRoleLeaf : ∀ a : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      IsLeaf H a → IsLeaf K (g a) := by
    intro a ha hLeaf
    have haL : a ∈ L :=
      finiteLeafMeetSupport_leaf_mem_L DH hLSource ha hLeaf
    exact hLTarget a haL
  have hRoleOne : ∀ s : Nat,
      s ∈ countableDiaryFiniteSupport H (m + 1) →
      IsOneSplit H s → IsOneSplit K (g s) := by
    intro s hs hOne
    obtain ⟨a,b,ha,hb,hab,hMeet⟩ :=
      finiteLeafMeetSupport_oneSplit_selected_witness
        DH hLSource hs hOne
    have hSA := hLSupport a ha
    have hSB := hLSupport b hb
    have hNe : g a ≠ g b := by
      rcases lt_or_gt_of_ne hab with hAB | hBA
      · exact ne_of_lt (C.ordered a b hSA hSB hAB)
      · exact Ne.symm (ne_of_lt (C.ordered b a hSB hSA hBA))
    have hRow :
        (H.oneMeetLevel a b, K.oneMeetLevel (q a) (q b)) ∈ T :=
      finiteLeafGeneratorTable_oneMeet H K L q a b ha hb hab
    have hForced :
        g (H.oneMeetLevel a b) =
          K.oneMeetLevel (q a) (q b) :=
      finiteGeneratorTableValue_eq_of_mem T C.functional _ _ hRow
    have hTargetMeet :
        g s = K.oneMeetLevel (g a) (g b) := by
      calc
        g s = g (H.oneMeetLevel a b) :=
          congrArg g hMeet.symm
        _ = K.oneMeetLevel (q a) (q b) := hForced
        _ = K.oneMeetLevel (g a) (g b) := by
          rw [hChosen a ha,hChosen b hb]
    rw [hTargetMeet]
    exact DK.singleton_meets (g a) (g b)
      (hLTarget a ha) (hLTarget b hb) hNe
  have hRoleTwo : ∀ s : Nat,
      s ∈ countableDiaryFiniteSupport H (m + 1) →
      IsTwoSplit H s → IsTwoSplit K (g s) := by
    intro s hs hTwo
    obtain ⟨a,b,c,d,ha,hb,hc,hd,hab,hcd,hMeet⟩ :=
      finiteLeafMeetSupport_twoSplit_selected_witness
        DH hLSource hs hTwo
    have hSA := hLSupport a ha
    have hSB := hLSupport b hb
    have hSC := hLSupport c hc
    have hSD := hLSupport d hd
    have hRow :
        (H.twoMeetLevel a b c d,
          K.twoMeetLevel (q a) (q b) (q c) (q d)) ∈ T :=
      finiteLeafGeneratorTable_twoMeet H K L q
        a b c d ha hb hc hd hab hcd
    have hForced :
        g (H.twoMeetLevel a b c d) =
          K.twoMeetLevel (q a) (q b) (q c) (q d) :=
      finiteGeneratorTableValue_eq_of_mem T C.functional _ _ hRow
    have hTargetMeet :
        g s = K.twoMeetLevel (g a) (g b) (g c) (g d) := by
      calc
        g s = g (H.twoMeetLevel a b c d) :=
          congrArg g hMeet.symm
        _ = K.twoMeetLevel (q a) (q b) (q c) (q d) := hForced
        _ = K.twoMeetLevel (g a) (g b) (g c) (g d) := by
          rw [hChosen a ha,hChosen b hb,hChosen c hc,hChosen d hd]
    have hTargetAB : g a < g b := C.ordered a b hSA hSB hab
    have hTargetCD : g c < g d := C.ordered c d hSC hSD hcd
    have h2Support :
        2 ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_marker H L 2 (by omega)
    have hg2 : g 2 = 2 :=
      finiteGeneratorTableValue_eq_of_mem T C.functional 2 2
        (finiteLeafGeneratorTable_marker H K L q 2 (by omega))
    have hsAbove : 2 < g s := by
      have hs3 : 3 ≤ s := hTwo.1
      have hOrd := C.ordered 2 s h2Support hs (by omega)
      change g 2 < g s at hOrd
      rw [hg2] at hOrd
      exact hOrd
    have hSourceLe :
        s ≤ min a c := by
      rw [← hMeet]
      exact H.twoMeetLevel_le_min a b c d
    have hNeA : s ≠ a := by
      intro heq
      have ht : IsTwoSplit H a := by simpa only [heq] using hTwo
      exact (hLSource a ha).2.2 ht.2.2
    have hNeC : s ≠ c := by
      intro heq
      have ht : IsTwoSplit H c := by simpa only [heq] using hTwo
      exact (hLSource c hc).2.2 ht.2.2
    have hSourceLtA : s < a := by
      have hLe : s ≤ a := hSourceLe.trans (min_le_left _ _)
      omega
    have hSourceLtC : s < c := by
      have hLe : s ≤ c := hSourceLe.trans (min_le_right _ _)
      omega
    have hTargetLtA : g s < g a :=
      C.ordered s a hs hSA hSourceLtA
    have hTargetLtC : g s < g c :=
      C.ordered s c hs hSC hSourceLtC
    rcases DK.pair_meets
        (g a) (g b) (g c) (g d)
        hTargetAB hTargetCD
        (hLTarget a ha) (hLTarget b hb)
        (hLTarget c hc) (hLTarget d hd) with
      hCap | hMarker | hSplit
    · have hCapImage : g s = min (g a) (g c) :=
        hTargetMeet.trans hCap
      omega
    · have hMarkerImage : g s = 1 :=
        hTargetMeet.trans hMarker
      omega
    · rw [hTargetMeet]
      exact hSplit
  exact {
    functional := C.functional
    leaf := hNewLeaf
    range := C.range
    ordered := C.ordered
    leaf_role := hRoleLeaf
    one_split_role := hRoleOne
    two_split_role := hRoleTwo
    induced_edge := C.induced_edge
  }

/-- Over genuine source/target diaries with the prescribed outer
leaf map, the reduced geometric table tests and the original
complete finite candidate tests are equivalent. -/
theorem iff_full
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t)) :
    ReducedFiniteNewLeafCandidateCondition H K F m f v ↔
    FiniteNewLeafCandidateCondition H K F m f v := by
  constructor
  · intro C
    exact C.to_full DH DK P hm hFleaf
  · intro C
    exact ⟨C.functional,C.range,C.ordered,C.induced_edge⟩


/-- Exact relative successor criterion with the redundant
role checks removed for a genuine diary target and prescribed
leaf-valued outer map. -/
theorem relative_successor_iff_reduced_candidate
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t)) :
    (∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        g a = f a) ∧ g m = v) ↔
    ReducedFiniteNewLeafCandidateCondition H K F m f v := by
  exact (AdmissibleCofinalDiaryStage.relative_successor_iff_finite_candidate
    DH P hm v).trans (iff_full DH DK P hm hFleaf).symm

end ReducedFiniteNewLeafCandidateCondition

/-- Conditional countable diary unavoidability with a smaller,
more geometrically transparent finite realization obligation.
Because source/target are genuine diaries and the prescribed F-image
already consists of actual target leaves, no independent finite
role checks are required: S1/S2 and strict order provide them.

The remaining finite hypothesis still asks for correct edge/nonedge
incidence, a functional numerical generator table, and a future-order
reserve at EVERY new source leaf. No theorem produces those values. -/
theorem exists_fullDiaryEmbedding_of_reduced_reserved_candidates
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F : Nat → Nat)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (hRealize : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        ReservedDiaryStage H K F m f →
        ∃ v : Nat,
          ReducedFiniteNewLeafCandidateCondition H K F m f v ∧
          FutureOrderReserve H (m + 1)
            (candidateNewLeafTableMap H K m f v)) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  apply exists_fullDiaryEmbedding_of_reserved_new_leaf_extensions DH DK F
  intro m hm f hf
  obtain ⟨v,hReduced,hReserve⟩ := hRealize m hm f hf
  obtain ⟨g,Q,hKeep,hNew,hReserveG⟩ :=
    (AdmissibleCofinalDiaryStage.reserved_successor_iff_finite_reserved_candidate
      DH hf.1 hm v).mpr
        ⟨hReduced.to_full DH DK hf.1 hm hFleaf,hReserve⟩
  exact ⟨g,⟨Q,hReserveG⟩,hKeep⟩

end DiaryLeafPriority
end ThreeUniformDiaries
