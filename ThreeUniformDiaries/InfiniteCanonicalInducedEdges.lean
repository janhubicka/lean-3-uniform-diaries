import ThreeUniformDiaries.InfiniteCanonicalSelectedTriples
import ThreeUniformDiaries.TypeRepresentation

/-!
# Concrete infinite canonical maps preserve induced 3-hypergraph edges

The abstract CanonicalMap structure has an enum_triple_compat field.
For the actual recursively constructed E0 map of an infinite geometric
strong picture, that formula is not assumed: it follows from the
already verified selected-triple theorem in direct ordered-hypergraph
predicate language.

This is the edge component of the manuscript canonical-map lemma and
of the eventual proof of the decoded infinite self-embedding.
The singleton/auxiliary type relations at nonselected target
coordinates and full map composition are separate obligations.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The concrete infinite canonical E0 map is an induced embedding on
the selected vertex indices of every finite enumerated source. -/
theorem infiniteEnumCanonicalMap_induced_edges
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (N : Nat) (H : EnumNode N)
    (i j k : Nat) (hij : i < j) (hjk : j < k) (hkN : k < N) :
    ((infiniteEnumCanonicalMap h₀ h₁ h₂ N H).val.toOrdered3Graph).edge
      (f i) (f j) (f k) ↔ H.toOrdered3Graph.edge i j k := by
  change
    (infiniteEnumCanonicalMap h₀ h₁ h₂ N H).val.triple
      (f i) (f j) (f k) = true ↔ H.triple i j k = true
  rw [infiniteEnumCanonicalMap_selectedTriple
    h₀ h₁ h₂ hf N i j k hij hjk hkN H]

end CoordNode
end ThreeUniformDiaries
