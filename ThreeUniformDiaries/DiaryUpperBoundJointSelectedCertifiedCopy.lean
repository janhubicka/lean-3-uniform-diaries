import ThreeUniformDiaries.DiaryUpperBoundUnorderedLeafCopyNoGeneric

/-!
# Track A: a SINGLE jointly selected sharp ordinary copy and certified fusion suffices

English-first adversarial proof: 3-uniform-diaries PR #335.
The earlier sharp diary upper theorem assumes CERTIFIED fusion for
EVERY unordered ordinary selfcopy w of U. Its actual proof first
selects ONE w by the already checked finite ATR sharp ordinary
upper and then uses the certificate ONLY FOR THAT w.

This theorem isolates the sharper one-selected-w interface:
given ONE ordinary selfembedding w with an exact labelled palette
on the pulled-back genuine leaf colour, plus ONE independent
CertifiedDiaryFusionData on the SAME leaf range F∘w, obtain a
marker-fixed TypeRespecting diary selfembedding with that palette
on EVERY genuine target diary-leaf labelled A-copy.

This is a conditional proof interface, NOT existence of a joint
Ramsey/certified choice; it does not prove the circular printed
upper theorem, countable diary unavoidability, or sharp degrees.
No auxiliary-to-diary transfer is smuggled into the proof.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A sharp ordinary Ramsey colour copy w and certified fusion
FOR EXACTLY THE SAME w imply the sharp labelled full diary
upper palette. Unlike older APIs, no ∀ w certified-fusion
hypothesis is required, and F need not be ordered or leaf-surjective.
The finite colour-bound hypothesis is precisely on ACTUAL labelled
induced A-copies in U and their F∘w-images in H. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_upper_of_joint_selected_copy
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {v : Fin a → Nat // IsDiaryLeafLabelledCopy A H v} → κ)
    (w : UnorderedEmbedding U U)
    (palette : List κ)
    (hLength : palette.length =
      (∑ P ∈ allIncreasingPresentations A,
        (unmarkedDiariesOfIncreasingPresentation A P).card) *
      Fintype.card (FiniteHypergraphAut A.toOrdered3Graph a))
    (hSharp : ∀ v : Fin a → Nat,
      ∀ hv : IsInducedLabelledCopy A U v,
        χ ⟨(fun i => F (w (v i))),
          ⟨isInducedLabelledCopy_map_unordered
              A F (fun i => w (v i))
              (isInducedLabelledCopy_map_unordered A w v hv),
           fun i => hLeaf (w (v i))⟩⟩ ∈ palette)
    (hCertified : CertifiedDiaryFusionData D H
      (fun t : Nat => F (w t))) :
    ∃ (h : Ordered3Graph.Embedding H H)
      (L : List κ),
        L.length =
          (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        h.TypeRespecting ∧
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        ∀ v : Fin a → Nat,
          IsDiaryLeafLabelledCopy A H v →
          ∃ hOutput :
              IsDiaryLeafLabelledCopy A H (fun i => h (v i)),
            χ ⟨(fun i => h (v i)), hOutput⟩ ∈ L := by
  classical
  obtain ⟨h, hType, hMarkers, hRange⟩ :=
    exists_typeRespecting_fullDiaryEmbedding_of_certified_fusion
      D D (fun t => F (w t)) hCertified
  refine ⟨h, palette, hLength, hType, hMarkers, ?_⟩
  intro v hv
  let q : Fin a → Nat := fun i =>
    Classical.choose (hRange (v i) (hv.2 i))
  have hImage (i : Fin a) :
      h (v i) = F (w (q i)) :=
    Classical.choose_spec (hRange (v i) (hv.2 i))
  have hCopyImage : IsInducedLabelledCopy A H
      (fun i => h (v i)) :=
    isInducedLabelledCopy_map_unordered A h.asUnordered v hv.1
  have hEq : (fun i : Fin a => h (v i)) =
      (fun i : Fin a => F (w (q i))) := by
    funext i
    exact hImage i
  have hCopyInRange : IsInducedLabelledCopy A H
      (fun i => F (w (q i))) := by
    rw [← hEq]
    exact hCopyImage
  let Fw : UnorderedEmbedding U H := F.comp w
  have hQ : IsInducedLabelledCopy A U q :=
    isInducedLabelledCopy_pullback_unordered A Fw q hCopyInRange
  have hLeafImage :
      ∀ i : Fin a, IsLeaf H (h (v i)) := by
    intro i
    rw [hImage i]
    exact hLeaf (w (q i))
  have hOutput : IsDiaryLeafLabelledCopy A H
      (fun i => h (v i)) :=
    ⟨hCopyImage, hLeafImage⟩
  let target :
      {s : Fin a → Nat // IsDiaryLeafLabelledCopy A H s} :=
    ⟨(fun i => F (w (q i))),
      ⟨isInducedLabelledCopy_map_unordered A F
        (fun i => w (q i))
        (isInducedLabelledCopy_map_unordered A w q hQ),
        fun i => hLeaf (w (q i))⟩⟩
  have hTargetColour : χ target ∈ palette := by
    have hb := hSharp q hQ
    change χ target ∈ palette at hb
    exact hb
  have hSubtypeEq :
      (⟨(fun i => h (v i)), hOutput⟩ :
        {s : Fin a → Nat // IsDiaryLeafLabelledCopy A H s}) =
      target := by
    apply Subtype.ext
    exact hEq
  refine ⟨hOutput, ?_⟩
  rw [hSubtypeEq]
  exact hTargetColour

end ATRFiniteDecoder
end ThreeUniformDiaries
