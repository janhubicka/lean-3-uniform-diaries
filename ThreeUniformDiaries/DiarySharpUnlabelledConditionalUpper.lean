import ThreeUniformDiaries.DiaryMarkedUnmarkedGlobalCount
import ThreeUniformDiaries.DiaryUpperBoundCopyPalette

/-!
# Track C: sharp finite upper palette for unlabelled hypergraph copies

The marked finite-diary family and its projection to unmarked
finite diary sources are already finite and deduplicated.
For UNLABELLED A-copies, one colour task per underlying diary
source suffices: source automorphisms only permute the markings,
which have the same image as a finite vertex set.

We show that a factorisation of every LABELLED A-copy through
a genuine marked finite ATR source gives the exact shape-level
factorisation required by the already verified unlabelled-copy
palette theorem, with NO extra Aut(A) multiplier.

The precise finite ATR factorisation is EXPLICITLY assumed.
This theorem does not prove that every copy admits such a code,
does not identify the unmarked source family with an ambiguous
manuscript diary count, and does not establish a lower bound.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- In a genuinely marked full finite diary, the image of the
complete marking is exactly the set of ALL genuine source leaves.
This is a literal Finset equality, not a cardinality argument. -/
theorem genuineMarkedDiaryShape_markedLeaves_eq_positions
    {a : Nat} (A : EnumNode a)
    (T : MarkedFiniteSource 0 a)
    (hT : IsGenuineMarkedDiaryShape A T) :
    ((Finset.univ : Finset (Fin a)).image T.marked) =
      T.source.leafPositions := by
  classical
  let H := T.source.picture.toOrdered3Graph
  have hLeaves :
      ∀ i : Fin a, IsLeaf H (T.marked i).val := by
    intro i
    exact hT.2.2.1 i
  have hCover :
      ∀ u : Nat, 3 ≤ u → u < T.source.k + 1 →
        IsLeaf H u → ∃ i : Fin a, (T.marked i).val = u := by
    intro u hu3 hum hLeaf
    exact hT.2.2.2 u hu3 hum hLeaf
  ext j
  constructor
  · intro hj
    obtain ⟨i, _, hij⟩ := Finset.mem_image.mp hj
    have hLeaf : IsLeaf H j.val := by
      rw [← hij]
      exact hLeaves i
    simpa only [ProtectedSource.leafPositions,
      Finset.mem_filter, Finset.mem_univ, true_and] using hLeaf
  · intro hj
    have hLeaf : IsLeaf H j.val := by
      simpa only [ProtectedSource.leafPositions,
        Finset.mem_filter, Finset.mem_univ, true_and] using hj
    obtain ⟨i, hi⟩ :=
      hCover j.val hLeaf.1 j.isLt hLeaf
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, Fin.ext hi⟩

/-- Sharp *conditional* palette for colouring UNLABELLED copies:
one colour per genuine unmarked finite diary source. Starting with
actual marked finite ATR factorisation, forget the marks and
apply the previously verified shape-indexed copy-colour Ramsey
theorem. This avoids multiplying the unlabelled degree by Aut(A). -/
theorem actualFiniteAuxRamsey_direct_unlabelled_genuineDiaryCount
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (phi : UnorderedEmbedding K G.graph)
    (psi : UnorderedEmbedding G.graph K)
    (χ : Finset Nat → κ)
    (hFactors :
      ∀ v : Fin a → Nat,
        IsInducedLabelledCopy A K v →
        ∃ T ∈ allGenuineMarkedDiaryShapes A,
          ∃ e : T.source.Code G,
            ∀ i : Fin a, phi (v i) = e.image (T.marked i)) :
    ∃ w : UnorderedEmbedding K K,
      ∃ palette : List κ,
        palette.length = (allGenuineUnmarkedDiarySources A).card ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A K v →
          χ ((Finset.univ : Finset (Fin a)).image
            (fun i => w (v i))) ∈ palette := by
  classical
  let family : List (ProtectedSource 0) :=
    (allGenuineUnmarkedDiarySources A).toList
  have hShapeFactor :
      ∀ v : Fin a → Nat,
        IsInducedLabelledCopy A K v →
        ∃ S ∈ family, ∃ e : S.Code G,
          ((Finset.univ : Finset (Fin a)).image
            (fun i => phi (v i))) =
          S.leafPositions.image (fun j => e.image j) := by
    intro v hv
    obtain ⟨T, hT, e, he⟩ := hFactors v hv
    have hShape : IsGenuineMarkedDiaryShape A T :=
      (mem_allGenuineMarkedDiaryShapes_iff A T).mp hT
    have hTmem : T ∈ allGenuineMarkedDiaryFinset A :=
      (mem_allGenuineMarkedDiaryFinset_iff A T).mpr hShape
    have hSrcMem : T.source ∈ allGenuineUnmarkedDiarySources A :=
      Finset.mem_image.mpr ⟨T, hTmem, rfl⟩
    refine ⟨T.source, ?_, e, ?_⟩
    · simpa only [family, Finset.mem_toList] using hSrcMem
    · have hLeaves :=
        genuineMarkedDiaryShape_markedLeaves_eq_positions A T hShape
      calc
        ((Finset.univ : Finset (Fin a)).image
          (fun i => phi (v i))) =
          ((Finset.univ : Finset (Fin a)).image
            (fun i => e.image (T.marked i))) := by
            apply Finset.image_congr
            intro i _
            exact he i
        _ = (((Finset.univ : Finset (Fin a)).image T.marked).image
            (fun j => e.image j)) := by
            simp only [Finset.image_image, Function.comp_def]
        _ = T.source.leafPositions.image (fun j => e.image j) := by
            rw [hLeaves]
  obtain ⟨w, palette, hlength, hcolour⟩ :=
    actualFiniteAuxRamsey_direct_copy_palette_of_shape_factorisation
      G K A phi psi χ family hShapeFactor
  refine ⟨w, palette, ?_, hcolour⟩
  simpa only [family, Finset.length_toList] using hlength

end ATRFiniteDecoder
end ThreeUniformDiaries
