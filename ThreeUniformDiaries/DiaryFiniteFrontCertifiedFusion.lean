import ThreeUniformDiaries.DiaryCountableCertifiedFusion
import ThreeUniformDiaries.DiaryCofinalStageRestrictions
import ThreeUniformDiaries.DiaryCountableRelativeMarkerBase

/-!
# Track B: finitely many stage choices suffice for countable fusion

Existing CertifiedDiaryFusionData requires a nonempty, successor-closed
Safe predicate. This module constructs it from an inverse system of
NONEMPTY FINITE fronts of actual admissible diary support maps.

The essential hypothesis is not just existence of a finite embedding
at every stage: all later front maps must restrict, on the actual
finite meet support, to a member of each earlier front.

Define a stage to be Safe when it has a compatible extension at
arbitrarily large finite horizons. The finite next front makes Safe
successor-closed: if all its compatible elements died eventually,
the maximum of their finite failure horizons would contradict
the parent's arbitrarily long extensions.

This is precisely the finite-front compactness interface, not a
construction of bounded fronts from finite strong flip absorption.
No unconditional countable-source flip property is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Actual finite fronts of admissible maps over the canonical
finite leaf-meet supports S_m. Each map is total on Nat for
convenience, but compatibility only concerns the real support.

The finite-front hypothesis supplies FINITELY MANY possible maps
at every source stage (rather than merely individually finite
images). The backwards condition is a genuine restriction-closure
property for ALL surviving later maps. -/
structure FiniteCofinalDiaryFronts
    {H : Ordered3Graph Nat} (DH : RoleDiary H)
    (K : Ordered3Graph Nat) (F : Nat → Nat) where
  front : Nat → Finset (Nat → Nat)
  nonempty : ∀ m, (front m).Nonempty
  admissible : ∀ m f, f ∈ front m →
    AdmissibleCofinalDiaryStage H K F m f
  backward : ∀ m n, m ≤ n →
    ∀ g, g ∈ front n →
      ∃ f, f ∈ front m ∧ CofinalDiaryStageCompatible H m f g

namespace FiniteCofinalDiaryFronts

variable {H K : Ordered3Graph Nat} {DH : RoleDiary H}
variable {F : Nat → Nat}

/-- A front element survives every larger finite horizon; a
chosen future map may depend on the horizon. The next theorem
uses FINITENESS to obtain one child surviving all horizons. -/
def Safe (P : FiniteCofinalDiaryFronts DH K F)
    (m : Nat) (f : Nat → Nat) : Prop :=
  f ∈ P.front m ∧
    ∀ n, m ≤ n →
      ∃ g, g ∈ P.front n ∧
        CofinalDiaryStageCompatible H m f g

/-- Every actual admissible stage-zero map is a safe root.
Its support consists solely of markers 0,1,2, whose images
are fixed by every admissible map at every later stage. -/
theorem safe_zero_of_mem
    (P : FiniteCofinalDiaryFronts DH K F)
    (f : Nat → Nat) (hf : f ∈ P.front 0) :
    P.Safe 0 f := by
  refine ⟨hf, ?_⟩
  intro n hn
  obtain ⟨g,hg⟩ := P.nonempty n
  refine ⟨g,hg,?_⟩
  intro u hu
  have hu3 : u < 3 := by
    rw [countableDiaryFiniteSupport_zero_eq] at hu
    exact Finset.mem_range.mp hu
  have hF : f u = u := by
    have V := P.admissible 0 f hf
    rcases (show u = 0 ∨ u = 1 ∨ u = 2 by omega) with h | h | h
    · subst u
      exact V.marker_zero
    · subst u
      exact V.marker_one
    · subst u
      exact V.marker_two
  have hG : g u = u := by
    have V := P.admissible n g hg
    rcases (show u = 0 ∨ u = 1 ∨ u = 2 by omega) with h | h | h
    · subst u
      exact V.marker_zero
    · subst u
      exact V.marker_one
    · subst u
      exact V.marker_two
  exact hG.trans hF.symm

theorem exists_safe_zero
    (P : FiniteCofinalDiaryFronts DH K F) :
    ∃ f, P.Safe 0 f := by
  obtain ⟨f,hf⟩ := P.nonempty 0
  exact ⟨f,P.safe_zero_of_mem f hf⟩

/-- Finite-front König step, proved directly by a maximal
failure horizon argument rather than assuming a selected
coherent path. No forward extension hypothesis is assumed
for an arbitrary front element; only safe elements extend. -/
theorem safe_next
    (P : FiniteCofinalDiaryFronts DH K F)
    (m : Nat) (f : Nat → Nat)
    (hf : P.Safe m f) :
    ∃ g, P.Safe (m+1) g ∧
      CofinalDiaryStageCompatible H m f g := by
  classical
  by_contra hNone
  have hFailure :
      ∀ g, g ∈ P.front (m+1) →
        ∃ N, m+1 ≤ N ∧
          ∀ h, h ∈ P.front N →
            ¬ (CofinalDiaryStageCompatible H m f g ∧
                CofinalDiaryStageCompatible H (m+1) g h) := by
    intro g hg
    by_cases hFG : CofinalDiaryStageCompatible H m f g
    · have hNoFuture :
          ¬ (∀ N, m+1 ≤ N →
            ∃ h, h ∈ P.front N ∧
              CofinalDiaryStageCompatible H (m+1) g h) := by
        intro hFuture
        exact hNone ⟨g,⟨hg,hFuture⟩,hFG⟩
      push_neg at hNoFuture
      obtain ⟨N,hN,hNo⟩ := hNoFuture
      refine ⟨N,hN,?_⟩
      intro h hh hBoth
      exact (hNo h hh) hBoth.2
    · refine ⟨m+1,le_rfl,?_⟩
      intro h hh hBoth
      exact hFG hBoth.1
  let obstacle (g : Nat → Nat) : Nat :=
    if hg : g ∈ P.front (m+1) then
      Classical.choose (hFailure g hg)
    else 0
  let N := max (m+1) ((P.front (m+1)).sup obstacle)
  have hMN : m+1 ≤ N := le_max_left _ _
  have hBound (g : Nat → Nat) (hg : g ∈ P.front (m+1)) :
      obstacle g ≤ N := by
    exact (Finset.le_sup hg).trans (le_max_right _ _)
  obtain ⟨h,hh,hFH⟩ := hf.2 N (by omega)
  obtain ⟨g,hg,hGH⟩ :=
    P.backward (m+1) N hMN h hh
  have hFG : CofinalDiaryStageCompatible H m f g := by
    intro u hu
    have huNext : u ∈ countableDiaryFiniteSupport H (m+1) :=
      countableDiaryFiniteSupport_mono H m (m+1) (by omega) hu
    exact (hGH u huNext).symm.trans (hFH u hu)
  let ng := Classical.choose (hFailure g hg)
  have hNg : m+1 ≤ ng :=
    (Classical.choose_spec (hFailure g hg)).1
  have hNoG : ∀ x, x ∈ P.front ng →
      ¬ (CofinalDiaryStageCompatible H m f g ∧
          CofinalDiaryStageCompatible H (m+1) g x) :=
    (Classical.choose_spec (hFailure g hg)).2
  have hNgN : ng ≤ N := by
    have hEq : obstacle g = ng := by
      simp [obstacle,hg,ng]
    exact hEq ▸ hBound g hg
  obtain ⟨x,hx,hXH⟩ :=
    P.backward ng N hNgN h hh
  have hGX : CofinalDiaryStageCompatible H (m+1) g x := by
    intro u hu
    have huNg : u ∈ countableDiaryFiniteSupport H ng :=
      countableDiaryFiniteSupport_mono H (m+1) ng hNg hu
    exact (hXH u huNg).symm.trans (hGH u hu)
  exact (hNoG x hx) ⟨hFG,hGX⟩

/-- Canonical pruned certified subsystem extracted from finite
fronts. Note that Safe depends on the future front system:
the theorem does not magically prove that concrete finite
strong absorbers have compatible bounded fronts. -/
noncomputable def toCertified
    (P : FiniteCofinalDiaryFronts DH K F) :
    CertifiedDiaryFusionData DH K F where
  Safe := P.Safe
  valid := by
    intro m f hf
    exact P.admissible m f hf.1
  initial := P.exists_safe_zero
  next := by
    intro m f hf
    exact P.safe_next m f hf

/-- From bounded, nonempty restriction-closed finite fronts
to one genuine induced countable diary embedding. All nonmarker
numerical singleton and full pair meets are preserved, and
genuine leaves land in the specified F-range.

This is a CONDITIONAL compactness transfer theorem, not an
unconditional countable source absorption result. -/
theorem exists_full_embedding
    (P : FiniteCofinalDiaryFronts DH K F)
    (DK : RoleDiary K) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  exact (P.toCertified).exists_full_embedding DK

end FiniteCofinalDiaryFronts
end DiaryLeafPriority
end ThreeUniformDiaries
