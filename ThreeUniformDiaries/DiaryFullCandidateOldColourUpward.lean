import ThreeUniformDiaries.DiaryCandidateHighOldCut
import ThreeUniformDiaries.DiaryNewLeafMaxSupport

/-!
# Track C: FULL finite candidate validity is upward closed within one old-cut colour

English-first proof and adversarial referee audit:
  janhubicka/3-uniform-diaries PR #321

Fix an ACTUAL old admissible source diary stage P, a true new SOURCE
leaf m, and ONE complete finite candidate C_v at target leaf v.
For any other TRUE target leaf w in the ORIGINAL prescribed F range,
with v<=w and the same COMPLETE mixed singleton colour at the
old-stage-fixed cut, all fields of FiniteNewLeafCandidateCondition
hold again at w.

The previous checked candidate modules transfer generator
functionality, the exact non-new S1/S2 numeric map values and all
induced E2/E3/E5 edge and nonedge tests, WITHOUT separate new
functionality or same-generator-profile assumptions.

The remaining role and strict order checks use the fact that m
is the MAXIMUM supported source coordinate, while every other
supported source vertex has its target image literally unchanged.
At m the target is a true leaf by hypothesis. No full target
RoleDiary axiom is used.

The result is still one-step. It does not assert that such a
first candidate v exists, that its colour is the generic winning
colour, or that a fixed next-leaf image survives all later horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One complete genuine finite candidate C_v at v transfers to a
later genuine target leaf w of the SAME complete old-cut colour
within the original F-range. Every finite generator row, role,
strict support order, E2/E3/E5 incidence and nonincidence is checked.

Only the TRUE target leaf role and prescribed range membership of w
are additional assumptions. No second functionality, same numerical
non-new generator record, inducedness or target full diary assumption
is needed. -/
theorem AdmissibleCofinalDiaryStage.full_candidate_of_later_same_oldCut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v w : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (C : FiniteNewLeafCandidateCondition H K F m f v)
    (hvw : v ≤ w)
    (hColour :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w)
    (hwLeaf : IsLeaf K w)
    (hwRange : ∃ t : Nat, w = F t) :
    FiniteNewLeafCandidateCondition H K F m f w := by
  classical
  have hv : oldStageTailCut H m f ≤ v :=
    P.full_candidate_newLeaf_ge_oldStageTailCut hm C
  obtain ⟨hFunW, hOther, hMapV, hMapW⟩ :=
    candidate_generator_maps_same_nonleaf_of_oldCut_colour
      hm f v w hv (hv.trans hvw) hColour C.functional
  have hInduced :
      ∀ a b c : Nat,
        a ∈ countableDiaryFiniteSupport H (m+1) →
        b ∈ countableDiaryFiniteSupport H (m+1) →
        c ∈ countableDiaryFiniteSupport H (m+1) →
        a < b → b < c →
        (H.edge a b c ↔
          K.edge
            (candidateNewLeafTableMap H K m f w a)
            (candidateNewLeafTableMap H K m f w b)
            (candidateNewLeafTableMap H K m f w c)) :=
    (P.candidate_full_induced_of_later_same_oldCut_colour
      hm C hvw hColour).2
  refine {
    functional := hFunW
    leaf := hwLeaf
    range := hwRange
    ordered := ?_
    leaf_role := ?_
    one_split_role := ?_
    two_split_role := ?_
    induced_edge := hInduced
  }
  · intro a b ha hb hab
    have hbM : b ≤ m :=
      countableDiaryFiniteSupport_succ_le_new_leaf H m b hm hb
    by_cases hbm : b = m
    · subst b
      have ham : a ≠ m := ne_of_lt hab
      have hAv :
          candidateNewLeafTableMap H K m f v a < v := by
        have h := C.ordered a m ha hb hab
        simpa only [hMapV] using h
      have hAw := hOther a ha ham
      rw [← hAw, hMapW]
      exact lt_of_lt_of_le hAv hvw
    · have ham : a ≠ m := by omega
      rw [← hOther a ha ham, ← hOther b hb hbm]
      exact C.ordered a b ha hb hab
  · intro a ha hLeafA
    by_cases ham : a = m
    · subst a
      rw [hMapW]
      exact hwLeaf
    · rw [← hOther a ha ham]
      exact C.leaf_role a ha hLeafA
  · intro a ha hOne
    by_cases ham : a = m
    · subst a
      exact False.elim (hm.2.1 hOne.2.1)
    · rw [← hOther a ha ham]
      exact C.one_split_role a ha hOne
  · intro a ha hTwo
    by_cases ham : a = m
    · subst a
      exact False.elim (hm.2.2 hTwo.2.2)
    · rw [← hOther a ha ham]
      exact C.two_split_role a ha hTwo

/-- Under a FULL source RoleDiary, the exact finite-candidate iff
turns the preceding upward closure into an ACTUAL relative
admissible immediate successor at any later true F-range leaf
of the same complete old-stage mixed colour.

The old selected source leaves remain literally fixed, but
this one-step result is not a persistent all-horizon diary
embedding and does not assert a reserved future-order gap. -/
theorem AdmissibleCofinalDiaryStage.exists_relative_successor_of_later_same_oldCut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v w : Nat}
    (DH : RoleDiary H)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (C : FiniteNewLeafCandidateCondition H K F m f v)
    (hvw : v ≤ w)
    (hColour :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w)
    (hwLeaf : IsLeaf K w)
    (hwRange : ∃ t : Nat, w = F t) :
    ∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        g a = f a) ∧
      g m = w := by
  exact (P.relative_successor_iff_finite_candidate DH hm w).mpr
    (P.full_candidate_of_later_same_oldCut_colour
      hm C hvw hColour hwLeaf hwRange)

end DiaryLeafPriority
end ThreeUniformDiaries
