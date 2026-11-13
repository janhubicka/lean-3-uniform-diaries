import ThreeUniformDiaries.DiaryBoundedFamilyBareCandidateGenericAvoidance
import ThreeUniformDiaries.DiaryCofinalStageRestrictions

/-!
# Track C: reserve-free old-stage bare finite-candidate generic obstruction

English-first adversarial proof and scope audit:
  janhubicka/3-uniform-diaries PR #340.

The previously CI-verified Track C generic bare-candidate no-go was
presented for RESERVED old stages, but the proof never invoked the
future-order reserve field. In fact the complete finite candidate's
functional table and inducedness force the literal source-required
old-pair E5 bit over ANY actual old ADMISSIBLE diary stage.

This yields a whole UNORDERED induced generic refinement beyond every
target cutoff whose every vertex defeats ALL old admissible support
maps f with f(b)<B, and a finite-family version avoiding every
member's complete good old-cut colour palette. No prior or future
FutureOrderReserve field is needed.

Restricting an admissible next-stage map to the old source support
then forces its old selected leaf b to move beyond B if its new image
lies in the chosen refinement.

The generic refinements here are UNORDERED, not proved
AuxTypeRespecting. The results do not refute jointly selecting old
support and refinement or demonstrate a persistent countable branch.
The original verified reserved-stage APIs are retained unchanged.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The old-pair E5 bit is a necessary condition for a complete BARE
finite candidate over an actual admissible old stage. The old
future-order reserve condition is entirely irrelevant. -/
theorem AdmissibleCofinalDiaryStage.bare_candidate_preserves_old_pair_E5
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m a b v : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
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
    P.functional_candidate_table_preserves_old_support C.functional
  have hNew :
      candidateNewLeafTableMap H K m f v m = v := by
    have hAtM := C.chosen_selected_leaf m hmSelected
    simpa [candidateLeafImage] using hAtM
  have hEdge :=
    C.induced_edge a b m haNext hbNext hmNext hab hbm
  simpa only [hOldMap a haOld, hOldMap b hbOld, hNew] using hEdge


/-- One whole induced unordered generic copy simultaneously defeats
the BARE complete finite candidates of ALL actual old ADMISSIBLE
stages f whose second selected old leaf b maps below B. -/
theorem exists_generic_subcopy_avoiding_all_bounded_admissible_bare_candidates
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (B M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat,
        M < J n ∧ B < J n ∧
        IsLeaf K (J n) ∧
        (∃ t : Nat, J n = F t)) ∧
      (∀ f : Nat → Nat,
        AdmissibleCofinalDiaryStage H K (fun t : Nat => F t) m f →
        f b < B →
        ∀ n : Nat,
          ¬ FiniteNewLeafCandidateCondition
            H K (fun t : Nat => F t) m f (J n)) := by
  classical
  let chi : Nat → Nat → Bool :=
    fun _ _ => decide (¬ H.edge a b m)
  obtain ⟨J, hRange, hPattern⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
      G K F hFLeaf B M chi
  refine ⟨J, hRange, ?_⟩
  intro f P hBound n C
  have haS : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a ha
  have hbS : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) b hb
  have hOrder : f a < f b := P.ordered a b haS hbS hab
  have haLeaf : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  have hbLeaf : IsLeaf H b :=
    ((mem_countableDiaryLeafPrefix_iff H m b).mp hb).2.2
  obtain ⟨i, hi⟩ := P.leaf_range a haS haLeaf
  obtain ⟨j, hj⟩ := P.leaf_range b hbS hbLeaf
  have hTargetOrder : F i < F j := by
    simpa only [← hi, ← hj] using hOrder
  have hTargetBound : F j < B := by
    simpa only [← hj] using hBound
  have hOpp :
      K.edge (f a) (f b) (J n) ↔ ¬ H.edge a b m := by
    have hMask := hPattern n i j hTargetOrder hTargetBound
    simpa only [← hi, ← hj, chi, decide_eq_true_eq] using hMask
  have hCandidateBit :=
    P.bare_candidate_preserves_old_pair_E5 hm ha hb hab C
  have hImpossible : H.edge a b m ↔ ¬ H.edge a b m :=
    hCandidateBit.trans hOpp
  tauto


/-- One whole unordered generic copy defeats EVERY member of any
supplied finite family of actual old ADMISSIBLE stages, and avoids
each member's finite good old-cut colour palette. -/
theorem exists_generic_subcopy_avoiding_finite_admissible_stage_family_bare_palettes
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (k : Nat)
    (stages : Fin k → Nat → Nat)
    (hStages : ∀ i : Fin k, AdmissibleCofinalDiaryStage
      H K (fun t : Nat => F t) m (stages i))
    (M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      ∀ n : Nat,
        M < J n ∧ IsLeaf K (J n) ∧
        (∃ t : Nat, J n = F t) ∧
        (∀ i : Fin k,
          ¬ FiniteNewLeafCandidateCondition
            H K (fun t : Nat => F t) m (stages i) (J n) ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m (stages i)) (J n) ∉
            goodOldCutCandidateColours H K (fun t : Nat => F t)
              (stages i) m) := by
  classical
  let B : Nat :=
    (Finset.univ : Finset (Fin k)).sup (fun i => stages i b) + 1
  let Cut : Nat :=
    (Finset.univ : Finset (Fin k)).sup
      (fun i => oldStageTailCut H m (stages i))
  have hBound (i : Fin k) : stages i b < B := by
    have hSup :=
      Finset.le_sup (f := fun i : Fin k => stages i b)
        (Finset.mem_univ i)
    exact lt_of_le_of_lt hSup (Nat.lt_succ_self _)
  have hCut (i : Fin k) :
      oldStageTailCut H m (stages i) ≤ Cut :=
    Finset.le_sup
      (f := fun j : Fin k => oldStageTailCut H m (stages j))
      (Finset.mem_univ i)
  obtain ⟨J, hRange, hBad⟩ :=
    exists_generic_subcopy_avoiding_all_bounded_admissible_bare_candidates
      G F hFLeaf hm ha hb hab B (max M Cut)
  refine ⟨J, ?_⟩
  intro n
  obtain ⟨hLarge, _hB, hLeaf, t, hF⟩ := hRange n
  have hM : M < J n :=
    lt_of_le_of_lt (le_max_left M Cut) hLarge
  refine ⟨hM, hLeaf, ⟨t, hF⟩, ?_⟩
  intro i
  have hNoCandidate :
      ¬ FiniteNewLeafCandidateCondition
        H K F m (stages i) (J n) :=
    hBad (stages i) (hStages i) (hBound i) n
  have hAtCut : oldStageTailCut H m (stages i) ≤ J n :=
    (hCut i).trans
      ((le_max_right M Cut).trans hLarge.le)
  refine ⟨hNoCandidate, ?_⟩
  intro hInPalette
  exact hNoCandidate
    (((hStages i).full_candidate_iff_good_oldCut_colour
      hm hAtCut hLeaf ⟨t, hF⟩).mpr hInPalette)

/-- For an entire induced UNORDERED generic refinement J, every actual
admissible next-stage support map whose new source leaf lands in J
must move its selected old leaf b beyond B, regardless of the
FutureOrderReserve predicate. The statement is conditional on a
stage witness; later we can add nonvacuity from finite unavoidability. -/
theorem exists_generic_refinement_forcing_admissible_old_support_escape
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (B M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ g : Nat → Nat,
        AdmissibleCofinalDiaryStage H K (fun t : Nat => F t) (m + 1) g →
        ∀ n : Nat, g m = J n → B ≤ g b) := by
  classical
  obtain ⟨J, hRange, hBad⟩ :=
    exists_generic_subcopy_avoiding_all_bounded_admissible_bare_candidates
      G F hFLeaf hm ha hb hab B M
  refine ⟨J, ?_, ?_⟩
  · intro n
    exact ⟨(hRange n).1, (hRange n).2.2.1,
      (hRange n).2.2.2⟩
  · intro g Q n hNew
    by_contra hNot
    have hBound : g b < B := by omega
    have P : AdmissibleCofinalDiaryStage
        H K (fun t : Nat => F t) m g :=
      Q.restrict (Nat.le_succ m)
    have hKeep : ∀ a : Nat,
        a ∈ countableDiaryLeafPrefix H m → g a = g a := by
      intro a ha
      rfl
    have C : FiniteNewLeafCandidateCondition
        H K (fun t : Nat => F t) m g (J n) :=
      AdmissibleCofinalDiaryStage.relative_successor_implies_finite_candidate
        (f := g) Q hm hKeep hNew
    exact (hBad g P hBound n) C

end DiaryLeafPriority
end ThreeUniformDiaries
