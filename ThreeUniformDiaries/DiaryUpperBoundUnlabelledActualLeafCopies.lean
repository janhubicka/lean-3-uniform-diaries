import ThreeUniformDiaries.DiaryUpperBoundUnlabelledCofinalHorizonBounds

/-!
# Track A: sharp unlabelled upper on the ACTUAL subtype of leaf-copy vertex sets

The previously checked conditional unlabelled sharp diary upper accepts
a TOTAL colouring Finset Nat → κ.  The natural theorem colours only
genuine vertex sets of induced copies of the finite source A whose
vertices are diary leaves.  This module closes that domain alignment.

A genuine unlabelled diary-leaf A-copy is a finite vertex set S which
is the image of SOME induced labelled A-copy carried by genuine leaves.
Its definition is independent of any chosen labelling.  Extend a
colouring of its subtype to ALL finite sets using an arbitrary default
colour, apply the checked total-colouring theorem, and restrict back.
No division by the automorphism group or new geometric bound is used.

This does not prove the still-open cofinal next-leaf boundedness
assumption or unconditional countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- An ACTUAL unlabelled finite A-copy on genuine diary leaves is
a finite vertex set with some induced bijective enumeration from A.
This is the copy predicate, NOT a colouring of arbitrary Finsets. -/
def IsDiaryLeafUnlabelledCopy
    {a : Nat} (A : EnumNode a) (H : Ordered3Graph Nat)
    (S : Finset Nat) : Prop :=
  ∃ v : Fin a → Nat, IsDiaryLeafLabelledCopy A H v ∧
    (Finset.univ : Finset (Fin a)).image v = S

/-- Sharp unlabelled upper for an ARBITRARY colouring of the
SUBTYPE of ACTUAL genuine diary-leaf A-copies.

The output colours have a palette of the exact unmarked full diary
sum, with NO automorphism multiplier.  The output map is a
marker-fixed TypeRespecting induced diary selfembedding.  This
depends on the explicit, still-unproved cofinal horizon image bound. -/
theorem actualFiniteAuxRamsey_allDiaryLeaf_unlabelled_upper_onActualCopies_of_cofinalHorizonBounds
    (U H : Ordered3Graph Nat)
    (D : RoleDiary H)
    (F : UnorderedEmbedding U H)
    (hLeaf : ∀ t : Nat, IsLeaf H (F t))
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : {S : Finset Nat // IsDiaryLeafUnlabelledCopy A H S} → κ)
    (hBounds : HasCofinalHorizonBoundedNextLeafImages D F) :
    ∃ (h : Ordered3Graph.Embedding H H)
      (palette : List κ),
        palette.length =
          (∑ P ∈ allIncreasingPresentations A,
            (unmarkedDiariesOfIncreasingPresentation A P).card) ∧
        h.TypeRespecting ∧
        (h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2) ∧
        ∀ S : Finset Nat,
          IsDiaryLeafUnlabelledCopy A H S →
          ∃ hOutput : IsDiaryLeafUnlabelledCopy A H (S.image h),
            χ ⟨S.image h, hOutput⟩ ∈ palette := by
  classical
  let χAll : Finset Nat → κ := fun S =>
    if hS : IsDiaryLeafUnlabelledCopy A H S
    then χ ⟨S, hS⟩
    else Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨h, palette, hLen, hType, hMarkers, hColour⟩ :=
    actualFiniteAuxRamsey_allDiaryLeaf_unlabelled_upper_of_cofinalHorizonBounds
      U H D F hLeaf hUniversal A χAll hBounds
  refine ⟨h, palette, hLen, hType, hMarkers, ?_⟩
  intro S hS
  obtain ⟨v, hv, hSet⟩ := hS
  obtain ⟨hvOutput, hBound⟩ := hColour v hv
  have hSetImage :
      ((Finset.univ : Finset (Fin a)).image (fun j => h (v j))) =
        S.image h := by
    calc
      ((Finset.univ : Finset (Fin a)).image (fun j => h (v j))) =
          (((Finset.univ : Finset (Fin a)).image v).image h) := by
        simp only [Finset.image_image, Function.comp_def]
      _ = S.image h := by rw [hSet]
  have hCopy : IsDiaryLeafUnlabelledCopy A H (S.image h) :=
    ⟨(fun j => h (v j)), hvOutput, hSetImage⟩
  refine ⟨hCopy, ?_⟩
  have hAllBound : χAll (S.image h) ∈ palette := by
    rw [← hSetImage]
    exact hBound
  simpa only [χAll, dif_pos hCopy] using hAllBound

end ATRFiniteDecoder
end ThreeUniformDiaries
