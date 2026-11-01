import ThreeUniformDiaries.DiaryGenericFixedTwoEmbedding
import ThreeUniformDiaries.FiniteAuxEmbeddingPostcomposition

/-!
# Track A: transport any actual finite ATR diary code into the generic hypergraph

The upper-bound proof first builds the literal finite auxiliary
embedding of a leaf-generated support into its countable full diary.
The finite Ramsey theorem, however, colours actual finite codes in
the enumerated generic 3-hypergraph.

The verified universal K_I construction supplies a global
auxiliary-type-respecting induced embedding of ANY countable ordered
source H into the enumerated generic G, fixing markers 0 and 1.
Postcomposition of actual Fin m codes through that embedding is
already verified.

This module combines these interfaces without imposing an
infinite zero-extended source tail on the finite code. Every
prescribed marked image is transported LITERALLY, not replaced
by an arbitrary isomorphic copy.

This step does not require countable diary unavoidability,
a diary-specific source, or the final Ramsey theorem.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- An arbitrary enumerated source 3-hypergraph has a genuine
AUXILIARY-type-respecting induced copy in generic G, fixing
both initial marker vertices 0 and 1. The earlier API exposed
only the weaker TypeRespecting fix-two corollary. -/
theorem exists_auxTypeRespecting_embedding_fix_two
    (G : GenericEnumerated3Graph)
    (H : Ordered3Graph Nat) :
    ∃ ψ : Embedding H G.graph,
      ψ.AuxTypeRespecting ∧ ψ 0 = 0 ∧ ψ 1 = 1 := by
  obtain ⟨ψ,haux,hfix⟩ :=
    exists_auxTypeRespecting_embedding_fix_prefix
      G H 2 (by omega) (initialSegment_two_eq H G.graph)
  exact ⟨ψ,haux,hfix 0 (by omega),hfix 1 (by omega)⟩

/-- Any actual finite ATR source code in an arbitrary countable
ordered graph H can be composed through one global aux-type-
respecting diary-to-generic embedding. All genuine finite
source image coordinates are preserved by the exact formula
d(i)=ψ(e(i)), including arbitrary marked positions.

The target generic code is the same extensional `Fin m`
object consumed by the verified finite ATR Ramsey theorem. -/
theorem exists_generic_postcomposition_of_finiteAuxCode
    (G : GenericEnumerated3Graph)
    (K H : Ordered3Graph Nat) (m : Nat)
    (e : FiniteAuxEmbeddingImage H K m) :
    ∃ ψ : Embedding K G.graph,
      ψ.AuxTypeRespecting ∧ ψ 0 = 0 ∧ ψ 1 = 1 ∧
      ∃ d : FiniteAuxEmbeddingImage H G.graph m,
        ∀ i : Fin m, d.image i = ψ (e.image i) := by
  obtain ⟨ψ,hψ,h0,h1⟩ :=
    exists_auxTypeRespecting_embedding_fix_two G K
  refine ⟨ψ,hψ,h0,h1,e.postcompose ψ hψ, ?_⟩
  intro i
  exact FiniteAuxEmbeddingImage.postcompose_apply e ψ hψ i

end ATRFiniteDecoder
end ThreeUniformDiaries
