import ThreeUniformDiaries.DiaryLeafGeneratedStageCompatibility
import ThreeUniformDiaries.DiaryOneNewLeafSupportSuccessor

/-!
# A fresh leaf must preserve every old singleton and full pair meet

The old-marker/old-split edge profile of a fresh leaf is only one
necessary condition for a coherent successor. The *numerical meet*
of a pair or ordered pair of pairs involving the new leaf can already
have been fixed by the previous support. The target leaf must satisfy
all these previously fixed meet equations as well.

This module derives a genuinely finite set of necessary checks on
ONE proposed new target leaf value v, without assuming countable
fusion, an extension theorem, genericity, or a finite absorber.

These checks are NOT sufficient for a successor. In particular they
do not ensure new split roles, spacing, or compatibility of fresh
meet vertices not present in the previous finite support.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The leaf images proposed at a successor step: old leaves keep
their prescribed stage values, and the one new leaf m is sent to v. -/
def proposedFreshLeafImage
    (f : Nat → Nat) (m v u : Nat) : Nat :=
  if u = m then v else f u

/-- All already determined singleton/full pair meets on the next
finite selected-leaf prefix must evaluate to their OLD source-stage
images. The predicates are finite (the prefix and old support are
Finsets), but no claim of decidability of the externally prescribed
leaf range is made. -/
structure OldMeetLeafExtensionProfile
    (H K : Ordered3Graph Nat)
    (m : Nat) (f : Nat → Nat) (v : Nat) : Prop where
  oneMeet : ∀ a b : Nat,
    a ∈ countableDiaryLeafPrefix H (m + 1) →
    b ∈ countableDiaryLeafPrefix H (m + 1) →
    H.oneMeetLevel a b ∈ countableDiaryFiniteSupport H m →
    K.oneMeetLevel
      (proposedFreshLeafImage f m v a)
      (proposedFreshLeafImage f m v b) =
    f (H.oneMeetLevel a b)
  twoMeet : ∀ a b c d : Nat,
    a < b → c < d →
    a ∈ countableDiaryLeafPrefix H (m + 1) →
    b ∈ countableDiaryLeafPrefix H (m + 1) →
    c ∈ countableDiaryLeafPrefix H (m + 1) →
    d ∈ countableDiaryLeafPrefix H (m + 1) →
    H.twoMeetLevel a b c d ∈ countableDiaryFiniteSupport H m →
    K.twoMeetLevel
      (proposedFreshLeafImage f m v a)
      (proposedFreshLeafImage f m v b)
      (proposedFreshLeafImage f m v c)
      (proposedFreshLeafImage f m v d) =
    f (H.twoMeetLevel a b c d)

namespace AdmissibleCofinalDiaryStage

variable {H K : Ordered3Graph Nat} {F : Nat → Nat}
variable {m : Nat} {f g : Nat → Nat}

/-- Fixing old selected leaves makes the next step's leaf images
literal functions of the single proposed image g(m). -/
theorem successor_selected_leaf_image
    (hKeep : ∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
      g u = f u)
    (a : Nat)
    (ha : a ∈ countableDiaryLeafPrefix H (m + 1)) :
    g a = proposedFreshLeafImage f m (g m) a := by
  by_cases ham : a = m
  · subst a
    simp [proposedFreshLeafImage]
  · obtain ⟨ha3, ham1, haLeaf⟩ :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha
    have haOld : a ∈ countableDiaryLeafPrefix H m :=
      (mem_countableDiaryLeafPrefix_iff H m a).mpr
        ⟨ha3, by omega, haLeaf⟩
    simpa [proposedFreshLeafImage, ham] using hKeep a haOld

/-- Every admissible relative successor forces the complete
OLD one- and two-meet profile of the proposed new leaf. This is
strictly more than checking the mixed old-pair EDGE incidences. -/
theorem successor_forces_old_meet_profile
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g)
    (hKeep : ∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
      g u = f u) :
    OldMeetLeafExtensionProfile H K m f (g m) := by
  have hCompat : CofinalDiaryStageCompatible H m f g :=
    P.successor_compatible_of_selected_leaf_agreement Q hKeep
  have hSelectedLeaf :
      ∀ u : Nat, u ∈ countableDiaryLeafPrefix H (m + 1) →
        IsLeaf H u := by
    intro u hu
    exact ((mem_countableDiaryLeafPrefix_iff H (m + 1) u).mp hu).2.2
  have hSelectedSupport :
      ∀ u : Nat, u ∈ countableDiaryLeafPrefix H (m + 1) →
        u ∈ countableDiaryFiniteSupport H (m + 1) := by
    intro u hu
    exact mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) u hu
  constructor
  · intro a b ha hb hOld
    have hOne := Q.leaf_oneMeet a b
      (hSelectedSupport a ha) (hSelectedSupport b hb)
      (hSelectedLeaf a ha) (hSelectedLeaf b hb)
    have hA := successor_selected_leaf_image
      (H := H) (m := m) hKeep a ha
    have hB := successor_selected_leaf_image
      (H := H) (m := m) hKeep b hb
    calc
      K.oneMeetLevel
        (proposedFreshLeafImage f m (g m) a)
        (proposedFreshLeafImage f m (g m) b) =
          K.oneMeetLevel (g a) (g b) := by rw [← hA, ← hB]
      _ = g (H.oneMeetLevel a b) := hOne
      _ = f (H.oneMeetLevel a b) := hCompat _ hOld
  · intro a b c d hab hcd ha hb hc hd hOld
    have hTwo := Q.leaf_twoMeet a b c d
      (hSelectedSupport a ha) (hSelectedSupport b hb)
      (hSelectedSupport c hc) (hSelectedSupport d hd)
      hab hcd
      (hSelectedLeaf a ha) (hSelectedLeaf b hb)
      (hSelectedLeaf c hc) (hSelectedLeaf d hd)
    have hA := successor_selected_leaf_image
      (H := H) (m := m) hKeep a ha
    have hB := successor_selected_leaf_image
      (H := H) (m := m) hKeep b hb
    have hC := successor_selected_leaf_image
      (H := H) (m := m) hKeep c hc
    have hD := successor_selected_leaf_image
      (H := H) (m := m) hKeep d hd
    calc
      K.twoMeetLevel
        (proposedFreshLeafImage f m (g m) a)
        (proposedFreshLeafImage f m (g m) b)
        (proposedFreshLeafImage f m (g m) c)
        (proposedFreshLeafImage f m (g m) d) =
          K.twoMeetLevel (g a) (g b) (g c) (g d) := by
            rw [← hA, ← hB, ← hC, ← hD]
      _ = g (H.twoMeetLevel a b c d) := hTwo
      _ = f (H.twoMeetLevel a b c d) := hCompat _ hOld

/-- Failure of the prescribed old-meet equations for every
candidate target leaf is an independent no-extension certificate.
Nothing here supplies a positive realization theorem. -/
theorem no_successor_without_old_meet_profile
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hNo : ∀ v : Nat,
      ¬ OldMeetLeafExtensionProfile H K m f v) :
    ¬ ∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) := by
  rintro ⟨g, Q, hKeep⟩
  exact hNo (g m) (P.successor_forces_old_meet_profile Q hKeep)

end AdmissibleCofinalDiaryStage
end DiaryLeafPriority
end ThreeUniformDiaries
