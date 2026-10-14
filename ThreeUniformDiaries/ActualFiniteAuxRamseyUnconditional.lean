import ThreeUniformDiaries.ActualFiniteAuxRamsey
import ThreeUniformDiaries.UniversalAuxBranchEmbedding
import Milliken.GeneralTree.UnconditionalHLAPI

/-!
# Final unconditional aux-type Ramsey theorem, finite embedding domain

The checked universal heterogeneous Halpern–Läuchli induction in
lean-milliken yields HasBoundaryProductHL for the actual root-glued
E0/E1/E2 tree, with unbounded but locally finite branching.

The geometric ATR application proves the full finite Ramsey
conclusion from exactly that combinatorial input, using the actual
finite embedding image type, the complete K_I canonical branch
decoder and one fixed outer self-embedding chosen before the finite
embedding is quantified.

Here we discharge that last input by the unconditional upstream
theorem. This is the manuscript's nonempty finite A, matching-initial-
segment form; the vacuous incompatible-prefix case is separate.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder


/-- The actual nonempty finite Ramsey conclusion for aux-type-
respecting embeddings of A into the enumerated generic 3-hypergraph,
without any HL, Milliken, or synthetic realization assumption. -/
theorem actualFiniteAuxRamsey_unconditional
    (G : GenericEnumerated3Graph)
    {n k : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (I : EnumNode n)
    (hGI : G.graph.initialSegment n = I)
    (hAI : A.truncate n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1) → κ) :
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
        (∀ j < n, u j = j) ∧
        ∃ color : κ,
          ∀ e : Ordered3Graph.FiniteAuxEmbeddingImage
              A.toOrdered3Graph G.graph (k + 1),
            (∀ i : Fin (k + 1), i.val < n → e.image i = i.val) →
            χ (e.postcompose u hu) = color := by
  exact actualFiniteAuxRamsey_of_boundaryProductHL
    G hnk A I hGI hAI E phi hphi
    (Milliken.GeneralTree.boundaryProductHL_unconditional
      CoordNode.rootGluedAmbientTree) χ

/-- Presentation-free ATR Ramsey conclusion for finite A whose first n
vertices coincide with G. The universal K_I embedding is constructed
rather than assumed; no Milliken or synthetic realisation hypothesis
remains. The incompatible-prefix case is a separate obligation. -/
theorem actualFiniteAuxRamsey_matchingPrefix
    (G : GenericEnumerated3Graph)
    {n k : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (I : EnumNode n)
    (hGI : G.graph.initialSegment n = I)
    (hAI : A.truncate n = I)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph (k + 1) → κ) :
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
        (∀ j < n, u j = j) ∧
        ∃ color : κ,
          ∀ e : Ordered3Graph.FiniteAuxEmbeddingImage
              A.toOrdered3Graph G.graph (k + 1),
            (∀ i : Fin (k + 1), i.val < n → e.image i = i.val) →
            χ (e.postcompose u hu) = color := by
  obtain ⟨E, phi, hphi⟩ := exists_universal_auxEmbedding G I hGI
  exact actualFiniteAuxRamsey_unconditional
    G hnk A I hGI hAI E phi hphi χ

end ATRFiniteDecoder
end ThreeUniformDiaries
