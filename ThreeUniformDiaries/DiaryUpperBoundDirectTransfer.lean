import ThreeUniformDiaries.DiaryUpperBoundMarkedFiniteColours
import ThreeUniformDiaries.DiaryFiniteUniversalLeafRange

/-!
# Track A: direct big-Ramsey upper-bound transfer

The full lower-bound unavoidability theorem is NOT an input to an
upper-bound construction: given ordered induced phi : K -> G and
unordered induced psi : G -> K, any aux-respecting refinement
u : G -> G produces an UNORDERED induced self-copy of K,

    w = psi o u o phi.

The present theorem supplies this direct self-copy and its finite
colour palette from one explicitly formulated missing premise:
each labelled finite A-copy in K must admit a genuine finite
auxiliary-type-respecting source code for the prescribed tuple
phi(v_i) in G, with its distinguished positions among a finite
list of marked sources.

No claim is made that the latter geometric factorisation is yet
proved, or that the list length equals the manuscript diary count.
Those are genuine independent goals. The abstract direct transfer
does not use diary flip absorption, countable unavoidability, or
the final diary Ramsey theorem.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace Embedding

variable {H K : Ordered3Graph Nat}

/-- Every increasing induced ternary embedding is automatically
an induced embedding of the underlying UNORDERED 3-hypergraph.
All three source indices are increasing, but no order condition
on an arbitrary outer unordered embedding is being imposed. -/
def asUnordered (f : Embedding H K) : UnorderedEmbedding H K where
  toFun := f.toFun
  injective := f.strictMono.injective
  edge_iff := by
    intro a b c hab hbc
    calc
      H.unorderedEdge a b c ↔ H.edge a b c :=
        H.unorderedEdge_iff_of_lt a b c hab hbc
      _ ↔ K.edge (f a) (f b) (f c) :=
        f.edge_iff hab hbc
      _ ↔ K.unorderedEdge (f a) (f b) (f c) :=
        (K.unorderedEdge_iff_of_lt
          (f a) (f b) (f c)
          (f.strictMono hab) (f.strictMono hbc)).symm

end Embedding
end Ordered3Graph

namespace ATRFiniteDecoder

open Ordered3Graph

/-- An actual labelled finite induced embedding into the underlying
unordered K, not an ambient ordered embedding. The source has
precisely a vertices, so every embedding image is represented once
by the labelled function on Fin a. -/
def IsInducedLabelledCopy
    {a : Nat} (A : EnumNode a)
    (K : Ordered3Graph Nat) (v : Fin a → Nat) : Prop :=
  Function.Injective v ∧
    ∀ i j k : Fin a, i < j → j < k →
      (A.triple i.val j.val k.val = true ↔
        K.unorderedEdge (v i) (v j) (v k))

/-- A direct upper-bound theorem from an EXACT diary-envelope
factorisation premise. Given A, every labelled A-copy in K must
factor through one of the listed marked finite ATR source codes
after the fixed increasing induced map phi : K -> G.

The conclusion is a genuine UNORDERED induced self-embedding
of the ambient K with a colour palette of exactly the same list
length as the finite source family. It does NOT appeal to
countable diary unavoidability. Establishing factorisation for
the actual diary shapes, and the sharp count of shapes, remain open. -/
theorem actualFiniteAuxRamsey_direct_upper_of_factorisation
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (phi : Embedding K G.graph)
    (psi : UnorderedEmbedding G.graph K)
    (χ : (Fin a → Nat) → κ)
    (family : List (MarkedFiniteSource 0 a))
    (hFactors :
      ∀ v : Fin a → Nat,
        IsInducedLabelledCopy A K v →
        ∃ S ∈ family, ∃ e : S.source.Code G,
          ∀ i : Fin a, phi (v i) = e.image (S.marked i)) :
    ∃ w : UnorderedEmbedding K K,
      ∃ palette : List κ,
        palette.length = family.length ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A K v →
          χ (fun i => w (v i)) ∈ palette := by
  obtain ⟨u, hu, palette, hlen, hpalette⟩ :=
    actualFiniteAuxRamsey_markedPalette_zero
      G a psi.toFun χ family
  let w : UnorderedEmbedding K K :=
    psi.comp ((u.comp phi).asUnordered)
  refine ⟨w, palette, hlen, ?_⟩
  intro v hv
  have hfactor :
      ∃ S ∈ family, ∃ e : S.source.Code G,
        ∀ i : Fin a, phi (v i) = e.image (S.marked i) :=
    hFactors v hv
  have hc := hpalette (fun i => phi (v i)) hfactor
  change χ (fun i => psi (u (phi (v i)))) ∈ palette
  exact hc

end ATRFiniteDecoder
end ThreeUniformDiaries
