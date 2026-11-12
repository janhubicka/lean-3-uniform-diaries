import ThreeUniformDiaries.DiaryReservedOldColourTailDichotomy
import ThreeUniformDiaries.DiaryFiniteReservedCandidateCriterion
import ThreeUniformDiaries.DiaryReducedFiniteCandidateCriterion

/-!
# Track A: each old-cut colour is eventually entirely finite-candidate valid or empty

The checked exact finite successor criterion says that for a genuine
old reserved stage, the full S1/S2 numeric generator table test
(including all roles, induced edges and nonedges, leaf range and
FutureOrderReserve) is EQUIVALENT to an ACTUAL compatible
reserved immediate successor whose new leaf maps to v.

The checked complete old-stage mixed singleton-colour dichotomy
says that, for each finite colour c, actual compatible reserved
new-leaf images of that colour are either wholly absent or
upward closed along numerically later genuine prescribed range
leaves of the SAME colour. No genericity is assumed.

This module connects these statements WITHOUT introducing any
new relative-existence hypothesis: it proves that the entire
finite generator-table condition, and separately the reduced
E2/E3/E5 condition, obey precisely the same old-cut dichotomy.

This removes individual compatibility tests *within an already
anchored cofinal colour fibre*, but it does NOT produce an anchor,
force the generic-winning colour to be good, or make one fixed
next image persist through all later finite diary horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A complete finite numeric generator candidate with future reserve
is literally equivalent to a genuine old-support-compatible
reserved immediate successor with the proposed new image v.
The old stage P itself must already be reserved and actual. -/
theorem ReservedDiaryStage.finite_candidate_iff_compatible_next_leaf
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v : Nat}
    (DH : RoleDiary H)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m) :
    (FiniteNewLeafCandidateCondition H K F m f v ∧
      FutureOrderReserve H (m + 1)
        (candidateNewLeafTableMap H K m f v)) ↔
      HasCompatibleReservedNextLeaf H K F f m v := by
  constructor
  · rintro ⟨hCandidate, hReserve⟩
    obtain ⟨g, Q, hOld, hNew, hReserved⟩ :=
      (AdmissibleCofinalDiaryStage.reserved_successor_iff_finite_reserved_candidate
        DH P.1 hm v).mpr ⟨hCandidate, hReserve⟩
    have hCompat : CofinalDiaryStageCompatible H m f g :=
      P.1.successor_compatible_of_selected_leaf_agreement Q hOld
    exact ⟨g, ⟨Q, hReserved⟩, hCompat, hNew⟩
  · rintro ⟨g, Q, hCompat, hNew⟩
    have hOld : ∀ a : Nat,
        a ∈ countableDiaryLeafPrefix H m → g a = f a := by
      intro a ha
      exact hCompat a
        (mem_finiteLeafMeetSupport_leaf H
          (countableDiaryLeafPrefix H m) a ha)
    exact
      (AdmissibleCofinalDiaryStage.reserved_successor_iff_finite_reserved_candidate
        DH P.1 hm v).mp ⟨g, Q.1, hOld, hNew, Q.2⟩

/-- For EACH complete colour c at the cut chosen solely from the
fixed old reserved stage, either no proposed target image of c
passes the complete finite S1/S2 generator, role, induced edge,
range and future-reserve tests; OR after one finite threshold EVERY
genuine prescribed-range leaf of that same colour passes ALL tests.

A colour may be bounded or empty and no winning colour is asserted
to have a valid anchor. -/
theorem ReservedDiaryStage.finite_candidate_colour_fibre_all_or_none
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool) :
    (∀ v : Nat,
      (FiniteNewLeafCandidateCondition H K F m f v ∧
        FutureOrderReserve H (m + 1)
          (candidateNewLeafTableMap H K m f v)) →
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v ≠ c) ∨
    (∃ T : Nat, ∀ w : Nat, T ≤ w →
      IsLeaf K w → (∃ t : Nat, w = F t) →
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w = c →
      (FiniteNewLeafCandidateCondition H K F m f w ∧
        FutureOrderReserve H (m + 1)
          (candidateNewLeafTableMap H K m f w))) := by
  rcases (compatible_reserved_nextLeaf_colour_fibre_all_or_none
    (H := H) (K := K) (F := F) (f := f) (m := m)
    hm c) with hNone | ⟨T, hTail⟩
  · left
    intro v hCandidate
    exact hNone v
      ((P.finite_candidate_iff_compatible_next_leaf DH hm).mp
        hCandidate)
  · right
    refine ⟨T, ?_⟩
    intro w hTw hwLeaf hwRange hwColour
    exact (P.finite_candidate_iff_compatible_next_leaf
      DH hm).mpr (hTail w hTw hwLeaf hwRange hwColour)

/-- The same exact all-or-none statement for the SMALLER finite
candidate API, in which entire inducedness is checked using only
E2, E3 and E5 families. All source/target full RoleDiary
assumptions needed for the reduced exact criterion are explicit. -/
theorem ReservedDiaryStage.reduced_E2E3E5_candidate_colour_fibre_all_or_none
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool) :
    (∀ v : Nat,
      (FiniteNewLeafE2E3E5CandidateCondition H K F m f v ∧
        FutureOrderReserve H (m + 1)
          (candidateNewLeafTableMap H K m f v)) →
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v ≠ c) ∨
    (∃ T : Nat, ∀ w : Nat, T ≤ w →
      IsLeaf K w → (∃ t : Nat, w = F t) →
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w = c →
      (FiniteNewLeafE2E3E5CandidateCondition H K F m f w ∧
        FutureOrderReserve H (m + 1)
          (candidateNewLeafTableMap H K m f w))) := by
  rcases P.finite_candidate_colour_fibre_all_or_none
    DH hm c with hNone | ⟨T, hTail⟩
  · left
    intro v
    rintro ⟨C, hReserve⟩
    exact hNone v ⟨C.toFull DH DK, hReserve⟩
  · right
    refine ⟨T, ?_⟩
    intro w hw hwLeaf hwRange hwColour
    obtain ⟨C, hReserve⟩ :=
      hTail w hw hwLeaf hwRange hwColour
    exact ⟨C.toE2E3E5, hReserve⟩

end DiaryLeafPriority
end ThreeUniformDiaries
