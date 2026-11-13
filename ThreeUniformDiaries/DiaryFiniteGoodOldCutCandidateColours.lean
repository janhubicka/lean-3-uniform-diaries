import ThreeUniformDiaries.DiaryHighOldCutCandidateColourIff

/-!
# Track C: a FINITE palette exactly classifies all high complete finite candidates

English mathematical proof and adversarial referee audit:
  janhubicka/3-uniform-diaries PR #326

For a fixed old-stage map f and new genuine source leaf m, the
COMPLETE mixed singleton colours below the old-stage cut B form
a finite Boolean function palette. Define its good subset by
existentially witnessing an ACTUAL complete finite candidate
among genuine target leaves in the ORIGINAL prescribed F-range
at numerical levels >=B.

The exact high-colour candidate iff theorem says the ENTIRE
finite candidate predicate for ANY other genuine F-range leaf
w>=B is equivalent to membership of its complete B-colour
in this finite good palette. Therefore numeric S1/S2 generator
functionality, source-target role and order, and ALL induced
E2/E3/E5 edges/nonedges are exactly FINITE-COLOUR data in
the high old-stage tail.

This is NOT a claim that GoodColours is nonempty, or that
a global generic Ramsey-winning colour is good. It does
not include the separate RESERVED FutureOrderReserve or
fixed-image persistence through later source horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Finite palette of complete old-cut mixed singleton colours
which have AT LEAST ONE actual true F-range new-leaf candidate
above the old-stage-fixed cut B. No computable decision
procedure or existence of a good colour is asserted. -/
noncomputable def goodOldCutCandidateColours
    (H K : Ordered3Graph Nat) (F f : Nat → Nat)
    (m : Nat) :
    Finset (Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool) := by
  classical
  exact Finset.univ.filter (fun c =>
    ∃ v : Nat,
      oldStageTailCut H m f ≤ v ∧
      IsLeaf K v ∧ (∃ t : Nat, v = F t) ∧
      FiniteNewLeafCandidateCondition H K F m f v ∧
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v = c)

/-- Once the OLD admissible stage P and true new source leaf m
are fixed, the COMPLETE finite candidate predicate for all
genuine true target leaves in the ORIGINAL F-range above B
is EXACTLY membership of one finite set of complete B-colours.

No separate numerical generator profile, candidate-specific
cutoff beyond B, nor target full RoleDiary axiom is needed.
The finite good palette may be empty. -/
theorem AdmissibleCofinalDiaryStage.full_candidate_iff_good_oldCut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m w : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hw : oldStageTailCut H m f ≤ w)
    (hwLeaf : IsLeaf K w)
    (hwRange : ∃ t : Nat, w = F t) :
    FiniteNewLeafCandidateCondition H K F m f w ↔
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w ∈
      goodOldCutCandidateColours H K F f m := by
  classical
  simp only [goodOldCutCandidateColours, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro Cw
    exact ⟨w, hw, hwLeaf, hwRange, Cw, rfl⟩
  · rintro ⟨v, hv, hvLeaf, hvRange, Cv, hColour⟩
    exact P.full_candidate_of_same_oldCut_colour_high
      hm Cv hw hColour hwLeaf hwRange

/-- For a FULL source RoleDiary, the exact fixed-candidate iff
identifies genuine relative admissible one-leaf successor
existence above the old cut with the SAME finite good-colour
membership predicate. Old selected source leaf images remain
literally fixed; no future-order reserve or all-horizon
persistence is inferred. -/
theorem AdmissibleCofinalDiaryStage.relative_successor_iff_good_oldCut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m w : Nat}
    (DH : RoleDiary H)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hw : oldStageTailCut H m f ≤ w)
    (hwLeaf : IsLeaf K w)
    (hwRange : ∃ t : Nat, w = F t) :
    (∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        g a = f a) ∧ g m = w) ↔
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w ∈
      goodOldCutCandidateColours H K F f m := by
  calc
    _ ↔ FiniteNewLeafCandidateCondition H K F m f w :=
      P.relative_successor_iff_finite_candidate DH hm w
    _ ↔ _ :=
      P.full_candidate_iff_good_oldCut_colour hm hw hwLeaf hwRange

end DiaryLeafPriority
end ThreeUniformDiaries
