import ThreeUniformDiaries.DiaryCausalOriginalBranchV3
import ThreeUniformDiaries.DiaryCausalMarkerTypeTransport
import ThreeUniformDiaries.DiarySourceLexFirstAuxBit

/-!
# Causal marker gluing preserves every original proper singleton meet

The preceding original-branch V3 reduction assumed that exact
singleton meets are preserved. We now derive that assumption
directly from the causal marker equation.

For original leaves a,b whose raw singleton types first split
at m, assume the earlier off-branch masks on a,b agree below m.
The causal type-transport theorem then forces the completed
singleton types to agree THROUGH cut m.

The source first-difference theorem supplies an explicit raw
witness q<m with E_R(q,m,a) != E_R(q,m,b). Since the mask selects
no edge with middle vertex m, this witness remains different
in the completion. Therefore the final capped singleton meet
is EXACTLY m, not merely at least m.

Together with the unchanged meet column, this recovers the
literal LexEarlier comparison and BOTH Devlin marker clauses
on an original branch pair whose own mask is false.

These are abstract Nat-indexed graph statements. The remaining
sign-rooted step is to instantiate the mask coherences and
enumeration for every original flip branch, and to validate
the other pre-diary conditions and absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Causal marker extension preserves an original PROPER
singleton meet, provided the two terminal off-branch masks
are identical below the meet and the meet column itself
is unmasked. No diary axioms are required. -/
theorem causalMarkerLimit_preserves_original_proper_oneMeet
    (R : Ordered3Graph Nat)
    (mask : Nat → Nat → Prop)
    (hMaskLater : ∀ y z, mask y z → y < z)
    (m a b : Nat)
    (hma : m < a) (hmb : m < b)
    (hMeet : R.oneMeetLevel a b = m)
    (hMaskEq : SameEarlierMarkerMask mask m a b)
    (hNoMask : ∀ z : Nat, ¬ mask m z) :
    (causalMarkerLimit R mask).oneMeetLevel a b = m := by
  classical
  let G := causalMarkerLimit R mask
  have hRawTypes : R.SameOneTypeBelow m a b := by
    rw [← hMeet]
    exact R.oneMeetLevel_agree a b
  have hFinalTypes : G.SameOneTypeBelow m a b :=
    causalMarker_preserves_parent_oneType
      R G mask m a b hma.le hmb.le
      hRawTypes hMaskEq
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R mask hMaskLater x y a)
      (by
        intro x y hxy hys
        exact causalMarkerLimit_formula R mask hMaskLater x y b)
  have hMeetLow : m ≤ G.oneMeetLevel a b :=
    Nat.le_findGreatest (by omega) hFinalTypes
  let q := R.auxMeetLevel m a m b
  obtain ⟨hq,hRawDiff⟩ :=
    onePass_source_mixedAux_first_difference R m a b hma hmb hMeet
  have hColA : G.edge q m a ↔ R.edge q m a :=
    causalMarkerLimit_middle_unmasked
      R mask hMaskLater m hNoMask q a
  have hColB : G.edge q m b ↔ R.edge q m b :=
    causalMarkerLimit_middle_unmasked
      R mask hMaskLater m hNoMask q b
  have hFinalDiff : ¬ (G.edge q m a ↔ G.edge q m b) := by
    intro h
    exact hRawDiff (hColA.symm.trans (h.trans hColB))
  have hMeetHigh : G.oneMeetLevel a b ≤ m := by
    by_contra h
    have hmBefore : m < G.oneMeetLevel a b := by omega
    have hMustAgree : G.edge q m a ↔ G.edge q m b :=
      (G.oneMeetLevel_agree a b) hq hmBefore
    exact hFinalDiff hMustAgree
  exact Nat.le_antisymm hMeetHigh hMeetLow

/-- The V3 lexicographic direction on every original
leaf pair follows from prior-mask agreement and the
automatic exact singleton meet preservation. -/
theorem causalMarkerLimit_original_lex_of_mask_prefix
    (R : Ordered3Graph Nat)
    (mask : Nat → Nat → Prop)
    (hMaskLater : ∀ y z, mask y z → y < z)
    (m a b : Nat)
    (hma : m < a) (hmb : m < b)
    (hMeet : R.oneMeetLevel a b = m)
    (hMaskEq : SameEarlierMarkerMask mask m a b)
    (hNoMask : ∀ z : Nat, ¬ mask m z) :
    LexEarlier (causalMarkerLimit R mask) a b ↔
      LexEarlier R a b := by
  apply causalMarkerLimit_preserves_original_branch_lex
    R mask hMaskLater m a b hma hmb hMeet
  · exact causalMarkerLimit_preserves_original_proper_oneMeet
      R mask hMaskLater m a b hma hmb hMeet hMaskEq hNoMask
  · exact hNoMask

/-- Complete ORIGINAL-BRANCH V3 marker preservation, not just
the numerical lexicographic comparison. Both original
marker incidences are inherited on the unmasked branch pair;
the actual new lexicographic decision agrees with the raw one. -/
theorem causalMarkerLimit_preserves_original_pair_V3
    (R : Ordered3Graph Nat)
    (mask : Nat → Nat → Prop)
    (hMaskLater : ∀ y z, mask y z → y < z)
    (m a b : Nat)
    (hma : m < a) (hmb : m < b)
    (hMeet : R.oneMeetLevel a b = m)
    (hMaskEq : SameEarlierMarkerMask mask m a b)
    (hNoMaskMiddle : ∀ z : Nat, ¬ mask m z)
    (hNoMaskPair : ¬ mask a b)
    (hMarkerOne : R.edge 1 a b ↔ LexEarlier R a b)
    (hMarkerTwo : R.edge 2 a b ↔ ¬ LexEarlier R a b) :
    ((causalMarkerLimit R mask).edge 1 a b ↔
      LexEarlier (causalMarkerLimit R mask) a b) ∧
    ((causalMarkerLimit R mask).edge 2 a b ↔
      ¬ LexEarlier (causalMarkerLimit R mask) a b) := by
  have hLex := causalMarkerLimit_original_lex_of_mask_prefix
    R mask hMaskLater m a b hma hmb
    hMeet hMaskEq hNoMaskMiddle
  have hOne : (causalMarkerLimit R mask).edge 1 a b ↔
      R.edge 1 a b := by
    have hFormula := causalMarkerLimit_formula
      R mask hMaskLater 1 a b
    simpa [CausalMarkerColumn, hNoMaskPair] using hFormula
  have hTwo : (causalMarkerLimit R mask).edge 2 a b ↔
      R.edge 2 a b := by
    have hFormula := causalMarkerLimit_formula
      R mask hMaskLater 2 a b
    simpa [CausalMarkerColumn, hNoMaskPair] using hFormula
  exact ⟨(hOne.trans hMarkerOne).trans hLex.symm,
    (hTwo.trans hMarkerTwo).trans (not_congr hLex.symm)⟩

end DiaryLeafPriority
end ThreeUniformDiaries
