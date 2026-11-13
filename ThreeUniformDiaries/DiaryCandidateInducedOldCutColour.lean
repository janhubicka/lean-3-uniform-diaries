import ThreeUniformDiaries.DiaryCandidateFunctionalSameColour
import ThreeUniformDiaries.DiaryFunctionalCandidateFullInducedColourStability

/-!
# Track C: full induced finite candidate table transfers on ONE old-cut colour

English-first referee audit:
  janhubicka/3-uniform-diaries PR #317

The previously verified Track A terminal and all-supported induced
edge/nonedge stability lemma required (i) a functional SECOND proposed
candidate table, and (ii) literal equality of all proposed non-new
generator images. The new Track C old-cut row theorem and functionality
invariance prove BOTH automatically from a functional first table
and equality of ONE complete old-cut singleton colour, as long as
both proposed new target leaves are at least the old-stage cut.

This is a FINITE relative candidate-table stability result, not
unconditional existence of an actual successor, leaf roles/range,
numeric reserve, or all future-horizon persistence.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Complete new-candidate E2/E3/E5 inducedness and noninducedness
transfer from a genuine finite candidate v to any proposed w with
the SAME complete old-cut colour, provided v,w are numerically above
the old support cut.

There is NO additional second-table functionality or same-nonleaf
numeric generator-profile hypothesis: both follow by the new exact
finite generator row and functionality invariance theorems. -/
theorem AdmissibleCofinalDiaryStage.candidate_full_induced_of_same_oldCut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m v w : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (C : FiniteNewLeafCandidateCondition H K F m f v)
    (hv : oldStageTailCut H m f ≤ v)
    (hw : oldStageTailCut H m f ≤ w)
    (hColour :
      DiaryLowerBoundColors.singletonColour K (oldStageTailCut H m f) v =
        DiaryLowerBoundColors.singletonColour K (oldStageTailCut H m f) w) :
    FiniteGeneratorTableFunctional
        (candidateNewLeafGeneratorTable H K m f w) ∧
    (∀ a b c : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      b ∈ countableDiaryFiniteSupport H (m + 1) →
      c ∈ countableDiaryFiniteSupport H (m + 1) →
      a < b → b < c →
      (H.edge a b c ↔
        K.edge
          (candidateNewLeafTableMap H K m f w a)
          (candidateNewLeafTableMap H K m f w b)
          (candidateNewLeafTableMap H K m f w c))) := by
  obtain ⟨hFunctionalW, hSameNonleaf, _hMapV, _hMapW⟩ :=
    candidate_generator_maps_same_nonleaf_of_oldCut_colour
      hm f v w hv hw hColour C.functional
  exact ⟨hFunctionalW,
    P.candidate_full_induced_stable_of_old_cut_colour_and_profile
      hm C hFunctionalW hSameNonleaf hColour⟩

end DiaryLeafPriority
end ThreeUniformDiaries
