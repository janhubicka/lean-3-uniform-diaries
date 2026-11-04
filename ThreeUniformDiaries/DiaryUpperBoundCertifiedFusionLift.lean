import ThreeUniformDiaries.DiaryUpperBoundFullDiaryTypeRespectingLift
import ThreeUniformDiaries.DiaryCountableCertifiedFusion

/-!
# Track A: sharp diary upper lift from a certified subsystem of finite stages

The explicit all-reserved-stage candidate condition in the previously
verified sharp diary lift is sufficient but potentially too strong:
numerical future order room does not force the correct intermediate
split-role slots in the target. Track D's verified
CertifiedDiaryFusionData API instead permits a user-supplied Safe
predicate and only requires each SAFE stage to have a compatible
SAFE successor. Bad finite maps need never be selected.

This module isolates the exact Track A consequence of such a
certificate, without requiring Safe to be all reserved stages.
A certified family yields one induced limit with the initial
markers fixed, every nonmarker meet exact, and every source
leaf in the prescribed range. The separately verified marker
completion upgrades this to the manuscript's entire TypeRespecting
predicate (including marker-containing pair-type tests).

The sharp embedding-colouring upper bound then chooses an ordinary
unordered self-copy w and applies a supplied certified finite-stage
system for the target leaf range F[w[U]]. No upper Ramsey theorem
is used to prove existence of the certificate. The remaining input
is the ACTUAL certified-stage system, not countable unavoidability
or the final diary Ramsey theorem.

The certificate hypothesis is intentionally visible and unproved
in general. It could be fulfilled using a suitable role-sensitive
finite reserve; defining Safe in terms of the desired infinite
embedding would be circular and is not attempted here.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A genuine finite-stage fusion certificate yields one FULL
type-respecting, marker-fixed, induced countable diary embedding.
The certificate is an input: this theorem does not produce Safe. -/
theorem exists_typeRespecting_fullDiaryEmbedding_of_certified_fusion
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H)
    (DK : RoleDiary K)
    (F : Nat → Nat)
    (C : CertifiedDiaryFusionData DH K F) :
    ∃ e : Ordered3Graph.Embedding H K,
      e.TypeRespecting ∧
      (e 0 = 0 ∧ e 1 = 1 ∧ e 2 = 2) ∧
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) := by
  classical
  obtain ⟨P, hStageRange⟩ := C.exists_coherent
  obtain ⟨e, hEq, hOne, hTwo⟩ := P.exists_full_embedding DK
  have hSpec : DiaryPreembeddingSpec H K P.limit :=
    P.limit_is_diaryPreembedding
  have hMarkers : e 0 = 0 ∧ e 1 = 1 ∧ e 2 = 2 :=
    ⟨(hEq 0).trans hSpec.marker_zero,
      (hEq 1).trans hSpec.marker_one,
      (hEq 2).trans hSpec.marker_two⟩
  have hRange : ∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t := by
    intro u hu
    obtain ⟨t, ht⟩ := P.limit_leaf_range F hStageRange u hu
    exact ⟨t, (hEq u).trans ht⟩
  have hType : e.TypeRespecting :=
    e.typeRespecting_of_nonmarker_exact_meets_and_markers
      hMarkers.1 hMarkers.2.1 hMarkers.2.2 hOne hTwo
  exact ⟨e, hType, hMarkers, hRange⟩

/-- Sharp labelled upper palette on a genuinely TypeRespecting
diary self-copy, under a finite-stage certified-fusion system
for each candidate ordinary upper self-copy. Unlike the
all-reserved-stage theorem, this allows any independently
justified pruned/role-sensitive Safe predicate. -/
theorem actualFiniteAuxRamsey_fullDiary_upper_of_certified_fusion
    (G : GenericEnumerated3Graph)
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : Ordered3Graph.Embedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsInducedLabelledCopy A U v} → κ)
    (hCertified : ∀ w : UnorderedEmbedding U U,
      CertifiedDiaryFusionData D H (fun t => F (w t))) :
    ∃ (w : UnorderedEmbedding U U)
      (h : Ordered3Graph.Embedding H H)
      (palette : List κ),
        palette.length =
          (allGenuineUnmarkedDiarySources A).card *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        h.TypeRespecting ∧
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        (∀ u : Nat, IsLeaf H u →
          ∃ t : Nat, h u = F (w t)) ∧
        ∀ v : Fin a → Nat,
          ∀ hv : IsInducedLabelledCopy A U v,
            ∃ q : Fin a → Nat,
              ∃ hq : IsInducedLabelledCopy A U q,
                (∀ i : Fin a,
                  h (F (v i)) = F (w (q i))) ∧
                χ ⟨(fun i => w (q i)),
                  isInducedLabelledCopy_map_unordered A w q hq⟩ ∈ palette := by
  classical
  obtain ⟨w, palette, hLength, hBound⟩ :=
    actualFiniteAuxRamsey_sharp_upper_on_embeddings
      G U hUniversal A χ
  obtain ⟨h, hType, hMarkers, hRange⟩ :=
    exists_typeRespecting_fullDiaryEmbedding_of_certified_fusion
      D D (fun t => F (w t)) (hCertified w)
  refine ⟨w, h, palette, hLength, hType, hMarkers, hRange, ?_⟩
  intro v hv
  let q : Fin a → Nat := fun i =>
    Classical.choose (hRange (F (v i)) (hLeaf (v i)))
  have hImage (i : Fin a) :
      h (F (v i)) = F (w (q i)) :=
    Classical.choose_spec
      (hRange (F (v i)) (hLeaf (v i)))
  have hOldCopy : IsInducedLabelledCopy A H
      (fun i => h (F (v i))) :=
    isInducedLabelledCopy_map_unordered A h.asUnordered
      (fun i => F (v i))
      (isInducedLabelledCopy_map_unordered A F.asUnordered v hv)
  have hSame : (fun i : Fin a => h (F (v i))) =
      (fun i : Fin a => F (w (q i))) := by
    funext i
    exact hImage i
  have hNewCopy : IsInducedLabelledCopy A H
      (fun i => F (w (q i))) := by
    rw [← hSame]
    exact hOldCopy
  let FW : UnorderedEmbedding U H := F.asUnordered.comp w
  have hq : IsInducedLabelledCopy A U q :=
    isInducedLabelledCopy_pullback_unordered A FW q hNewCopy
  exact ⟨q, hq, hImage, hBound q hq⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
