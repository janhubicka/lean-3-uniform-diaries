import ThreeUniformDiaries.DiaryCandidateInducedOldCutColour
import ThreeUniformDiaries.DiaryReservedOldColourTailDichotomy
import ThreeUniformDiaries.DiaryFunctionalCandidateOldSupport

/-!
# Track C: a COMPLETE finite next-leaf candidate is already above the old cut

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #320

The fixed old-stage tail cut is the successor of the maximum
of all old finite support and selected old leaf target images.
If one proposed new target image v passes the COMPLETE finite
candidate test (including functionality and strict order),
the canonical new-leaf image at m is v, the old support
images are literally fixed by old-stage rigidity, and every
old supported source vertex lies STRICTLY before m. Therefore
all old support target images are <v and B≤v automatically.

With the newly submitted complete-colour functionality and
inducedness transfer lemmas, a LATER proposed new target image
w≥v of the same complete old-cut colour inherits functional
S1/S2 generator rows and the ENTIRE finite E2/E3/E5
induced edge/nonedge table, without separately assuming
w≥B, functionality of w's table, or same non-new profile.

This proves finite algebraic transfer, not target leaf range,
role validity, quantitative future reserve or existence of a
protected persistent next-leaf image.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A full finite candidate C at new leaf v necessarily places
v strictly AFTER EVERY old supported target image and in particular
at or above the old-stage-fixed numerical cut B.

No extra v≥B assumption is needed. This uses P as an ACTUAL old
admissible stage, C.functional and C.ordered on ALL generated
coordinates (including old S1/S2 splits), and the unique new
selected leaf row C.chosen_selected_leaf. -/
theorem AdmissibleCofinalDiaryStage.full_candidate_newLeaf_ge_oldStageTailCut
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (C : FiniteNewLeafCandidateCondition H K F m f v) :
    oldStageTailCut H m f ≤ v := by
  classical
  let L := countableDiaryLeafPrefix H m
  let S := countableDiaryFiniteSupport H m
  have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1, by omega, hm⟩
  have hmSupport : m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m hmSelected
  have hMapM : candidateNewLeafTableMap H K m f v m = v := by
    have h := C.chosen_selected_leaf m hmSelected
    simpa [candidateLeafImage] using h
  have hOld (u : Nat) (hu : u ∈ S) :
      candidateNewLeafTableMap H K m f v u = f u :=
    P.functional_candidate_table_preserves_old_support
      C.functional u hu
  have hOldBelow (u : Nat) (hu : u ∈ S) : f u < v := by
    have huLt : u < m :=
      countableDiaryFiniteSupport_lt_cut H m u hm.1 hu
    have huNew : u ∈ countableDiaryFiniteSupport H (m + 1) :=
      countableDiaryFiniteSupport_mono H m (m + 1)
        (by omega) hu
    have hOrder := C.ordered u m huNew hmSupport huLt
    rw [hOld u hu, hMapM] at hOrder
    exact hOrder
  have hvPos : 0 < v := by
    have hZero : 0 ∈ S :=
      mem_finiteLeafMeetSupport_marker H L 0 (by omega)
    have h := hOldBelow 0 hZero
    omega
  have hOldSup : S.sup f ≤ v - 1 := by
    apply Finset.sup_le
    intro u hu
    have h := hOldBelow u hu
    omega
  have hLeafSup : L.sup f ≤ v - 1 := by
    apply Finset.sup_le
    intro a ha
    have haS : a ∈ S :=
      mem_finiteLeafMeetSupport_leaf H L a ha
    have h := hOldBelow a haS
    omega
  change max (S.sup f) (L.sup f) + 1 ≤ v
  omega

/-- The second candidate's FINITE generator table and induced
edge/nonedge table follow from ONE complete old-cut singleton
colour, a full first candidate at v, and merely v≤w.

The numerical hypotheses B≤v,w of the preceding theorem are
now THEOREMS rather than additional assumptions. No target
role/range/future-reserve or actual next-stage existence at w
is claimed. -/
theorem AdmissibleCofinalDiaryStage.candidate_full_induced_of_later_same_oldCut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m v w : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (C : FiniteNewLeafCandidateCondition H K F m f v)
    (hvw : v ≤ w)
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
  have hv : oldStageTailCut H m f ≤ v :=
    P.full_candidate_newLeaf_ge_oldStageTailCut hm C
  exact P.candidate_full_induced_of_same_oldCut_colour
    hm C hv (hv.trans hvw) hColour

end DiaryLeafPriority
end ThreeUniformDiaries
