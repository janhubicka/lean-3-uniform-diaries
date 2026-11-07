import ThreeUniformDiaries.DiaryUpperBoundCofinalHorizonBounds
import ThreeUniformDiaries.DiarySharpUpperNoGenericParameter

/-!
# Track A: sharp UNLABELLED diary upper from cofinal bounded horizons

The checked exact unlabelled-copy big Ramsey upper palette has one
colour per distinct genuine unmarked full finite diary source:
there is NO factor |Aut(A)|. For the stronger conclusion of a
genuine TypeRespecting diary selfembedding, we use the same
INDEPENDENT finite-horizon fusion certificate as in the labelled
Track A upper theorem.

An ordinary induced upper copy w₀ stabilises arbitrary colourings of
finite vertex sets. Choose a further induced copy i with a cofinal
bounded-next-leaf-image certificate, yielding the verified countable
fusion selfembedding h with all genuine leaf images inside
F[w₀(i[U])]. Every genuine A-copy in the h-image pulls back to
an actual induced A-copy under F∘w₀∘i. Its finite set of images
therefore has one of the colours already stabilised by w₀.

No invented quotient by Aut(A), no loss of colour along relabelling,
and no countable unavoidability theorem is used. The cofinal
boundedness condition remains EXPLICIT and unproved.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A sharp, marker-fixed, fully TypeRespecting diary upper
bound on UNLABELLED genuine finite leaf copies. A colouring
of all finite vertex sets is restricted to those inducing
A on genuine H leaves; this is an admissible extension of
any finite colouring of actual unlabelled copies.

The palette length is the sum of genuine full diaries over
every increasing ordered presentation of unordered A, WITHOUT
an automorphism multiplier. The required cofinal next-leaf
bounds are a separate finite-stage geometric hypothesis. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_unlabelled_upper_of_cofinalHorizonBounds
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Finset Nat → κ)
    (hBounds : HasCofinalHorizonBoundedNextLeafImages D F) :
    ∃ (h : Ordered3Graph.Embedding H H)
      (palette : List κ),
        palette.length =
          (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) ∧
        h.TypeRespecting ∧
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        ∀ v : Fin a → Nat,
          IsDiaryLeafLabelledCopy A H v →
          ∃ hOutput :
              IsDiaryLeafLabelledCopy A H (fun j => h (v j)),
            χ ((Finset.univ : Finset (Fin a)).image
              (fun j => h (v j))) ∈ palette := by
  classical
  let χU : Finset Nat → κ := fun L => χ (L.image F)
  obtain ⟨w₀, palette, hLength, hBound⟩ :=
    actualFiniteAuxRamsey_sharp_unlabelled_upper_noGeneric
      U hUniversal A χU
  have hCofinal : HasCofinalCertifiedDiaryFusion D F :=
    hasCofinalCertifiedDiaryFusion_of_persistent_finite_covers
      D F hLeaf hUniversal
      ((cofinalHorizonBounds_iff_finiteNextLeafCovers D F).mp hBounds)
  obtain ⟨i, hC⟩ := hCofinal w₀
  let C : CertifiedDiaryFusionData D H (fun t => F (w₀ (i t))) :=
    Classical.choice hC
  let w : UnorderedEmbedding U U := w₀.comp i
  have hCertificate :
      CertifiedDiaryFusionData D H (fun t => F (w t)) := by
    change CertifiedDiaryFusionData D H (fun t => F (w₀ (i t)))
    exact C
  obtain ⟨h, hType, hMarkers, hRange⟩ :=
    exists_typeRespecting_fullDiaryEmbedding_of_certified_fusion
      D D (fun t => F (w t)) hCertificate
  refine ⟨h, palette, hLength, hType, hMarkers, ?_⟩
  intro v hv
  let q : Fin a → Nat := fun j =>
    Classical.choose (hRange (v j) (hv.2 j))
  have hImage (j : Fin a) :
      h (v j) = F (w (q j)) :=
    Classical.choose_spec (hRange (v j) (hv.2 j))
  have hCopyImage : IsInducedLabelledCopy A H (fun j => h (v j)) :=
    isInducedLabelledCopy_map_unordered A h.asUnordered v hv.1
  have hEq : (fun j : Fin a => h (v j)) =
      (fun j : Fin a => F (w (q j))) := by
    funext j
    exact hImage j
  have hCopyInRange : IsInducedLabelledCopy A H
      (fun j => F (w (q j))) := by
    rw [← hEq]
    exact hCopyImage
  let FW : UnorderedEmbedding U H := F.comp w
  have hQ : IsInducedLabelledCopy A U q :=
    isInducedLabelledCopy_pullback_unordered A FW q hCopyInRange
  have hRefinedCopy : IsInducedLabelledCopy A U
      (fun j => i (q j)) :=
    isInducedLabelledCopy_map_unordered A i q hQ
  have hLeafImage : ∀ j : Fin a, IsLeaf H (h (v j)) := by
    intro j
    rw [hImage j]
    exact hLeaf (w (q j))
  have hOutput : IsDiaryLeafLabelledCopy A H
      (fun j => h (v j)) :=
    ⟨hCopyImage, hLeafImage⟩
  have hSetEq :
      ((Finset.univ : Finset (Fin a)).image (fun j => h (v j))) =
      (((Finset.univ : Finset (Fin a)).image
        (fun j => w₀ (i (q j)))).image F) := by
    calc
      ((Finset.univ : Finset (Fin a)).image (fun j => h (v j))) =
          ((Finset.univ : Finset (Fin a)).image
            (fun j => F (w₀ (i (q j))))) := by
        apply Finset.image_congr
        intro j _
        exact hImage j
      _ = (((Finset.univ : Finset (Fin a)).image
            (fun j => w₀ (i (q j)))).image F) := by
        simp only [Finset.image_image, Function.comp_def]
  refine ⟨hOutput, ?_⟩
  have hBoundRef := hBound (fun j => i (q j)) hRefinedCopy
  change χ (((Finset.univ : Finset (Fin a)).image
    (fun j => w₀ (i (q j)))).image F) ∈ palette at hBoundRef
  rw [hSetEq]
  exact hBoundRef

end ATRFiniteDecoder
end ThreeUniformDiaries
