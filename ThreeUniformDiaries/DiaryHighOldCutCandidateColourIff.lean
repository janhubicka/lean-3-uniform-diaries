import ThreeUniformDiaries.DiaryFullCandidateOldColourUpward
import ThreeUniformDiaries.DiaryFunctionalCandidateOldCutBound
import ThreeUniformDiaries.DiaryNewLeafMaxSupport

/-!
# Track C: complete finite candidate legality is CONSTANT in each high old-cut colour

English mathematical proof and adversarial referee audit:
  janhubicka/3-uniform-diaries PR #323

The previous theorem gives upward closure in a complete old-stage
mixed singleton colour when the target new image w is LATER than
one actual complete candidate v. This bound v<=w is NOT needed
for the BARE finite candidate: its strict ordered support can
be checked from the OLD-STAGE-FIXED numerical cut B alone.

Once the first table at v is functional, the checked old-stage
bound forces every image of a supported source coordinate x≠m
strictly BELOW B=oldStageTailCut H m f. Thus ANY proposed w>=B
above the old cut preserves the strict order with all earlier
supported coordinates, regardless of whether w<v.

The now checked one-colour generator-table and inducedness
theorems give functionality of the second table, identical
old/nonleaf images and every induced edge AND nonedge E2/E3/E5
test. The only new role/range assumptions are the actual target
true-leaf condition on w and its membership in ORIGINAL F.

Consequently, for any two TRUE leaves v,w>=B of the same complete
B-colour, the entire FiniteNewLeafCandidateCondition is EQUIVALENT
between them, and with source RoleDiary H the actual relative
admissible successor-existence conditions are equivalent.

This is NOT the RESERVED future-order gap predicate:
FutureOrderReserve may fail at a smaller candidate even when
both candidates are above B. No anchored winning generic colour
or all-horizon persistent new-leaf image is constructed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A COMPLETE finite candidate at v transfers to ANY true
prescribed-range leaf w above the fixed old-stage cut B with
the same complete mixed singleton B-colour, WITHOUT assuming
v≤w. Thus a candidate's finite generator rows, order,
roles, and all induced E2/E3/E5 edges/nonedges are determined
on the high-B region by the full mixed colour.

The proof uses a bound strictly below B for EVERY image of a
supported source coordinate other than m from functionality
of the original candidate's generator table and the ACTUAL old
admissible stage P. No target full RoleDiary is required. -/
theorem AdmissibleCofinalDiaryStage.full_candidate_of_same_oldCut_colour_high
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v w : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (C : FiniteNewLeafCandidateCondition H K F m f v)
    (hw : oldStageTailCut H m f ≤ w)
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
  obtain ⟨hFunctionalW, hSame, _hMapV, hMapW⟩ :=
    candidate_generator_maps_same_nonleaf_of_oldCut_colour
      hm f v w hv hw hColour C.functional
  have hInduced :
      ∀ a b c : Nat,
        a ∈ countableDiaryFiniteSupport H (m + 1) →
        b ∈ countableDiaryFiniteSupport H (m + 1) →
        c ∈ countableDiaryFiniteSupport H (m + 1) →
        a < b → b < c →
        (H.edge a b c ↔
          K.edge
            (candidateNewLeafTableMap H K m f w a)
            (candidateNewLeafTableMap H K m f w b)
            (candidateNewLeafTableMap H K m f w c)) :=
    (P.candidate_full_induced_of_same_oldCut_colour
      hm C hv hw hColour).2
  refine {
    functional := hFunctionalW
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
      have hOldBelow :
          candidateNewLeafTableMap H K m f v a <
            oldStageTailCut H m f :=
        P.functional_candidate_other_below_oldStageTailCut
          hm C.functional ha ham
      rw [← hSame a ha ham, hMapW]
      exact lt_of_lt_of_le hOldBelow hw
    · have ham : a ≠ m := by omega
      rw [← hSame a ha ham, ← hSame b hb hbm]
      exact C.ordered a b ha hb hab
  · intro a ha hLeafA
    by_cases ham : a = m
    · subst a
      rw [hMapW]
      exact hwLeaf
    · rw [← hSame a ha ham]
      exact C.leaf_role a ha hLeafA
  · intro a ha hOne
    by_cases ham : a = m
    · subst a
      exact False.elim (hm.2.1 hOne.2.1)
    · rw [← hSame a ha ham]
      exact C.one_split_role a ha hOne
  · intro a ha hTwo
    by_cases ham : a = m
    · subst a
      exact False.elim (hm.2.2 hTwo.2.2)
    · rw [← hSame a ha ham]
      exact C.two_split_role a ha hTwo

/-- For TWO true target leaves v,w of the ORIGINAL prescribed F
range, both above the OLD-stage cut B, COMPLETE finite-candidate
validity at the genuine new source leaf m is an equivalence
whenever their complete singleton B-colours coincide.

The equivalence requires no numerical comparison v≤w or w≤v.
The independent Reserved future-gap predicate is NOT included. -/
theorem AdmissibleCofinalDiaryStage.full_candidate_iff_same_oldCut_colour_high
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v w : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hv : oldStageTailCut H m f ≤ v)
    (hw : oldStageTailCut H m f ≤ w)
    (hLeafV : IsLeaf K v) (hRangeV : ∃ t : Nat, v = F t)
    (hLeafW : IsLeaf K w) (hRangeW : ∃ t : Nat, w = F t)
    (hColour :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w) :
    (FiniteNewLeafCandidateCondition H K F m f v ↔
      FiniteNewLeafCandidateCondition H K F m f w) := by
  constructor
  · intro Cv
    exact P.full_candidate_of_same_oldCut_colour_high
      hm Cv hw hColour hLeafW hRangeW
  · intro Cw
    exact P.full_candidate_of_same_oldCut_colour_high
      hm Cw hv hColour.symm hLeafV hRangeV

/-- If the SOURCE H is a full RoleDiary, the checked fixed-candidate
iff converts the exact high colour-class equivalence above into
equivalence of existence of ACTUAL relative admissible immediate
successor stages with new target leaf images v and w.

This preserves all old SELECTED leaf images literally. It is not
a reserved future-gap or all-horizon persistence statement. -/
theorem AdmissibleCofinalDiaryStage.relative_successor_iff_same_oldCut_colour_high
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v w : Nat}
    (DH : RoleDiary H)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hv : oldStageTailCut H m f ≤ v)
    (hw : oldStageTailCut H m f ≤ w)
    (hLeafV : IsLeaf K v) (hRangeV : ∃ t : Nat, v = F t)
    (hLeafW : IsLeaf K w) (hRangeW : ∃ t : Nat, w = F t)
    (hColour :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w) :
    (∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        g a = f a) ∧ g m = v) ↔
    (∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        g a = f a) ∧ g m = w) := by
  calc
    _ ↔ FiniteNewLeafCandidateCondition H K F m f v :=
      P.relative_successor_iff_finite_candidate DH hm v
    _ ↔ FiniteNewLeafCandidateCondition H K F m f w :=
      P.full_candidate_iff_same_oldCut_colour_high
        hm hv hw hLeafV hRangeV hLeafW hRangeW hColour
    _ ↔ _ := (P.relative_successor_iff_finite_candidate DH hm w).symm

end DiaryLeafPriority
end ThreeUniformDiaries
