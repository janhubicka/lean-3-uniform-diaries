import ThreeUniformDiaries.DiaryCountableRelativeStepExtension
import ThreeUniformDiaries.DiaryCountableCoherentStageGluing
import ThreeUniformDiaries.DiaryMarkerMixedSingletonMeets

/-!
# Track B: genuine finite codes for bounded diary support maps

The countable fusion API uses total maps Nat -> Nat even though a
stage checks them only on a finite, leaf-meet-generated support S_m.

A support map may be normalised to zero outside S_m without changing
ANY admissible-stage obligation. The key nontrivial check is that all
source singleton and full pair meets of selected stage leaves still
lie inside S_m. This follows from the actual finite support
construction, not an unproved local finiteness shortcut.

If all supported images are bounded by b, these normalised maps form
a genuinely FINITE Finset: functions from the finite subtype S_m to
Fin b. This bridges image bounds to the finite-front compactness
framework, but it does NOT construct a restriction-closed family
at every stage or prove unrestricted countable-source absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Canonical representative of a total map on a finite support:
preserve exactly the values in S and put zero elsewhere. -/
def canonicalSupportMap (S : Finset Nat) (f : Nat → Nat) :
    Nat → Nat :=
  fun u => if u ∈ S then f u else 0

theorem canonicalSupportMap_eq_on
    (S : Finset Nat) (f : Nat → Nat) (u : Nat)
    (hu : u ∈ S) : canonicalSupportMap S f u = f u := by
  simp [canonicalSupportMap,hu]

theorem canonicalSupportMap_zero_outside
    (S : Finset Nat) (f : Nat → Nat) (u : Nat)
    (hu : u ∉ S) : canonicalSupportMap S f u = 0 := by
  simp [canonicalSupportMap,hu]

/-- Exhaustive finite collection of all canonical total maps
whose supported values are strictly below b. The code space
is the finite function type (S subtype) -> Fin b. -/
noncomputable def boundedSupportCodes (S : Finset Nat) (b : Nat) :
    Finset (Nat → Nat) := by
  classical
  exact (Finset.univ :
      Finset (({u : Nat // u ∈ S}) → Fin b)).image
        (fun code u => if hu : u ∈ S then
          (code ⟨u,hu⟩).val else 0)

/-- Any bounded map belongs to the finite canonical support
code collection after zero-extension outside S. -/
theorem canonicalSupportMap_mem_boundedSupportCodes
    (S : Finset Nat) (b : Nat) (f : Nat → Nat)
    (hBound : ∀ u, u ∈ S → f u < b) :
    canonicalSupportMap S f ∈ boundedSupportCodes S b := by
  classical
  unfold boundedSupportCodes
  apply Finset.mem_image.mpr
  refine ⟨(fun u : {u : Nat // u ∈ S} =>
    (⟨f u.val, hBound u.val u.property⟩ : Fin b)),
    Finset.mem_univ _, ?_⟩
  funext u
  by_cases hu : u ∈ S
  · simp [canonicalSupportMap,hu]
  · simp [canonicalSupportMap,hu]

/-- All values of a canonical bounded code at its supported
arguments lie below the given bound. -/
theorem boundedSupportCodes_mem_bound
    (S : Finset Nat) (b : Nat)
    (f : Nat → Nat)
    (hf : f ∈ boundedSupportCodes S b) :
    ∀ u, u ∈ S → f u < b := by
  classical
  unfold boundedSupportCodes at hf
  obtain ⟨code,_,rfl⟩ := Finset.mem_image.mp hf
  intro u hu
  simpa [hu] using (code ⟨u,hu⟩).isLt

/-- All admissible stage constraints survive canonical support
normalisation. In particular RHS meet images are still on the
support; this uses its exact one-/two-meet closure on selected
genuine source leaves. -/
theorem AdmissibleCofinalDiaryStage.normalize
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat)
    (P : AdmissibleCofinalDiaryStage H K F m f) :
    AdmissibleCofinalDiaryStage H K F m
      (canonicalSupportMap (countableDiaryFiniteSupport H m) f) := by
  classical
  let S := countableDiaryFiniteSupport H m
  have hEq (u : Nat) (hu : u ∈ S) :
      canonicalSupportMap S f u = f u :=
    canonicalSupportMap_eq_on S f u hu
  have hMarker (u : Nat) (hu : u < 3) : u ∈ S :=
    mem_finiteLeafMeetSupport_marker H
      (countableDiaryLeafPrefix H m) u hu
  have hOneMeet (a b : Nat)
      (ha : a ∈ S) (hb : b ∈ S)
      (hLa : IsLeaf H a) (hLb : IsLeaf H b) :
      H.oneMeetLevel a b ∈ S := by
    have haL : a ∈ countableDiaryLeafPrefix H m :=
      countableDiaryFiniteSupport_leaf_selected DH m a ha hLa
    have hbL : b ∈ countableDiaryLeafPrefix H m :=
      countableDiaryFiniteSupport_leaf_selected DH m b hb hLb
    by_cases hab : a = b
    · subst b
      rw [Ordered3Graph.oneMeetLevel_self_any H a]
      exact ha
    · exact mem_finiteLeafMeetSupport_oneMeet
        H (countableDiaryLeafPrefix H m) a b haL hbL hab
  have hTwoMeet (a b c d : Nat)
      (ha : a ∈ S) (hb : b ∈ S)
      (hc : c ∈ S) (hd : d ∈ S)
      (hab : a < b) (hcd : c < d)
      (hLa : IsLeaf H a) (hLb : IsLeaf H b)
      (hLc : IsLeaf H c) (hLd : IsLeaf H d) :
      H.twoMeetLevel a b c d ∈ S := by
    have haL := countableDiaryFiniteSupport_leaf_selected DH m a ha hLa
    have hbL := countableDiaryFiniteSupport_leaf_selected DH m b hb hLb
    have hcL := countableDiaryFiniteSupport_leaf_selected DH m c hc hLc
    have hdL := countableDiaryFiniteSupport_leaf_selected DH m d hd hLd
    exact mem_finiteLeafMeetSupport_twoMeet
      H (countableDiaryLeafPrefix H m)
      a b c d hab hcd haL hbL hcL hdL
  refine {
    ordered := ?_
    marker_zero := ?_
    marker_one := ?_
    marker_two := ?_
    leaf_role := ?_
    one_split_role := ?_
    two_split_role := ?_
    induced_edge := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
    leaf_range := ?_
  }
  · intro u v hu hv huv
    rw [hEq u hu,hEq v hv]
    exact P.ordered u v hu hv huv
  · rw [hEq 0 (hMarker 0 (by omega))]
    exact P.marker_zero
  · rw [hEq 1 (hMarker 1 (by omega))]
    exact P.marker_one
  · rw [hEq 2 (hMarker 2 (by omega))]
    exact P.marker_two
  · intro u hu hLeaf
    rw [hEq u hu]
    exact P.leaf_role u hu hLeaf
  · intro u hu hOne
    rw [hEq u hu]
    exact P.one_split_role u hu hOne
  · intro u hu hTwo
    rw [hEq u hu]
    exact P.two_split_role u hu hTwo
  · intro a b c ha hb hc hab hbc
    rw [hEq a ha,hEq b hb,hEq c hc]
    exact P.induced_edge a b c ha hb hc hab hbc
  · intro a b ha hb hLa hLb
    rw [hEq a ha,hEq b hb,hEq (H.oneMeetLevel a b)
        (hOneMeet a b ha hb hLa hLb)]
    exact P.leaf_oneMeet a b ha hb hLa hLb
  · intro a b c d ha hb hc hd hab hcd hLa hLb hLc hLd
    rw [hEq a ha,hEq b hb,hEq c hc,hEq d hd,
      hEq (H.twoMeetLevel a b c d)
        (hTwoMeet a b c d ha hb hc hd hab hcd hLa hLb hLc hLd)]
    exact P.leaf_twoMeet a b c d
      ha hb hc hd hab hcd hLa hLb hLc hLd
  · intro u hu hLeaf
    rw [hEq u hu]
    exact P.leaf_range u hu hLeaf

/-- A finite set of all bounded NORMALISED admissible stage
representatives. This is a code construction, not a nonemptiness
or relative extension theorem. -/
noncomputable def admissibleBoundedStageFront
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m b : Nat) : Finset (Nat → Nat) := by
  classical
  exact (boundedSupportCodes
      (countableDiaryFiniteSupport H m) b).filter
        (fun f => AdmissibleCofinalDiaryStage H K F m f)

/-- Any valid finite stage with a bound on all its supported
images produces an ACTUAL member of the finite candidate front. -/
theorem admissibleBoundedStageFront_contains_normalized
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (F : Nat → Nat)
    (m b : Nat) (f : Nat → Nat)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hBound : ∀ u, u ∈ countableDiaryFiniteSupport H m →
      f u < b) :
    canonicalSupportMap (countableDiaryFiniteSupport H m) f ∈
      admissibleBoundedStageFront H K F m b := by
  classical
  unfold admissibleBoundedStageFront
  apply Finset.mem_filter.mpr
  exact ⟨canonicalSupportMap_mem_boundedSupportCodes
      _ b f hBound, AdmissibleCofinalDiaryStage.normalize DH F m f P⟩

end DiaryLeafPriority
end ThreeUniformDiaries
