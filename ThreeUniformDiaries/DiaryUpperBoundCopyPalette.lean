import ThreeUniformDiaries.ActualFiniteAuxPalette
import ThreeUniformDiaries.DiaryUpperBoundDirectTransfer
import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Track B: direct finite-palette theorem for UNLABELLED hypergraph copies

A sharp copy-colouring upper bound needs ONE colour per full
finite diary SHAPE, not separate colours for each labelling of
its leaves. The labelled marked-source interface is useful for
general colours but creates an unnecessary factor for unlabelled
copies.

This theorem colours finite SETS of target vertices, and pulls
them back through the complete leaf set of each finite source
shape. It reuses the merged shape-indexed finite ATR palette
and composes ordinary induced embeddings of the UNORDERED
hypergraph reduct.

The sole geometric hypothesis says each finite unlabelled
A-copy maps (through the fixed outer embedding phi) onto the
complete leaf image of one genuinely finite ATR source shape.
No diary unavoidability, full diary Ramsey, type-to-aux inference,
or assumed equality with the sharp diary count is involved.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- The TRUE marked leaf positions of a finite enumerated source
shape. This definition is meaningful for arbitrary finite source
shapes; it does not itself assert the full diary V/E/S axioms. -/
noncomputable def ProtectedSource.leafPositions
    (S : ProtectedSource 0) : Finset (Fin (S.k + 1)) := by
  classical
  exact (Finset.univ : Finset (Fin (S.k + 1))).filter
    (fun i => DiaryLeafPriority.IsLeaf S.picture.toOrdered3Graph i.val)

/-- A direct finite colour bound for UNLABELLED induced A-copies.
The family is indexed only by source SHAPES, not by independently
marked occurrences. Each colour reads the entire leaf image.

The factorisation premise is explicit and must be proved by
canonical full-diary support extraction and genuine finite ATR
coding before using this theorem for the sharp big Ramsey bound.
The initial map K -> G need NOT preserve the numerical order. -/
theorem actualFiniteAuxRamsey_direct_copy_palette_of_shape_factorisation
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (phi : UnorderedEmbedding K G.graph)
    (psi : UnorderedEmbedding G.graph K)
    (χ : Finset Nat → κ)
    (family : List (ProtectedSource 0))
    (hFactors :
      ∀ v : Fin a → Nat,
        IsInducedLabelledCopy A K v →
        ∃ S ∈ family, ∃ e : S.Code G,
          ((Finset.univ : Finset (Fin a)).image
            (fun i => phi (v i))) =
          S.leafPositions.image (fun j => e.image j)) :
    ∃ w : UnorderedEmbedding K K,
      ∃ palette : List κ,
        palette.length = family.length ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A K v →
          χ ((Finset.univ : Finset (Fin a)).image
            (fun i => w (v i))) ∈ palette := by
  classical
  let colours : ∀ S : ProtectedSource 0, S.Code G → κ :=
    fun S e =>
      χ (S.leafPositions.image (fun j => psi (e.image j)))
  obtain ⟨u, hu, palette, hlength, hpalette⟩ :=
    actualFiniteAuxRamsey_zeroCut_palette G colours family
  let w : UnorderedEmbedding K K :=
    psi.comp ((u.asUnordered).comp phi)
  refine ⟨w, palette, hlength, ?_⟩
  intro v hv
  obtain ⟨S, hS, e, hsets⟩ := hFactors v hv
  have hnewsets :
      ((Finset.univ : Finset (Fin a)).image
        (fun i => psi (u (phi (v i))))) =
      S.leafPositions.image
        (fun j => psi (u (e.image j))) := by
    have h := congrArg
      (Finset.image (fun x : Nat => psi (u x))) hsets
    simpa only [Finset.image_image, Function.comp_def] using h
  have hmonochrome :
      χ (S.leafPositions.image
        (fun j => psi (u (e.image j)))) ∈ palette := by
    have hc := hpalette S hS e
    simpa only [colours, FiniteAuxEmbeddingImage.postcompose_apply]
      using hc
  change χ ((Finset.univ : Finset (Fin a)).image
      (fun i => psi (u (phi (v i))))) ∈ palette
  rw [hnewsets]
  exact hmonochrome

end ATRFiniteDecoder
end ThreeUniformDiaries
