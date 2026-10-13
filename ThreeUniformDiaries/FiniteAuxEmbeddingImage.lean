import ThreeUniformDiaries.ActualFiniteEmbeddingMeets
import ThreeUniformDiaries.AuxTypeRespectingComposition

/-!
# The genuinely finite domain of the ATR Ramsey colouring

The manuscript colours embeddings of a finite m-vertex hypergraph.
The existing type `Ordered3Graph.Embedding A.toOrdered3Graph G` has
source `Nat`, because `A.toOrdered3Graph` is a zero extension of A.
A colouring of those infinite maps may distinguish two embeddings
that agree at every vertex of A, and is therefore NOT the manuscript
colouring domain.

We make the finite domain explicit. A code consists of exactly the
m images, indexed by `Fin m`, together with the PROP that they admit
a strictly increasing global extension satisfying the genuine
FINITE source-edge and aux-type constraints. The extension is not
data, and the extensionality theorem shows that the tail never
affects identity or colouring.

The finite Aemb lemma already takes `FiniteAuxEmbedding` and hence
produces such codes. Any globally aux-type-respecting embedding also
restricts to one, with no use of a fictitious source tail in the
colouring. The reverse equivalence with purely bounded local `Fin m`
constraints can be established separately.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- The genuine finite m-vertex aux-type-respecting embedding code.
The tail extension is a proposition, not a field exposed to a
colouring; only the images on the real vertices constitute data. -/
structure FiniteAuxEmbeddingImage
    (H K : Ordered3Graph Nat) (m : Nat) where
  image : Fin m → Nat
  admissible : ∃ f : Nat → Nat,
    FiniteAuxEmbedding H K f m ∧
    ∀ i : Fin m, image i = f i.val

namespace FiniteAuxEmbeddingImage

variable {H K : Ordered3Graph Nat} {m : Nat}

/-- Two finite aux embeddings are equal precisely when all their
ACTUAL source-vertex images coincide, independently of any
chosen strictly increasing tail or admissibility proof. -/
@[ext] theorem ext (e d : FiniteAuxEmbeddingImage H K m)
    (h : ∀ i : Fin m, e.image i = d.image i) :
    e = d := by
  cases e with
  | mk e he =>
      cases d with
      | mk d hd =>
          have hfun : e = d := funext h
          subst d
          rfl

/-- Canonical finite-image code of an existing genuine finite
aux-type-respecting embedding. -/
def ofFiniteAuxEmbedding
    (f : Nat → Nat) (hf : FiniteAuxEmbedding H K f m) :
    FiniteAuxEmbeddingImage H K m where
  image := fun i => f i.val
  admissible := ⟨f, hf, fun _ => rfl⟩

@[simp] theorem ofFiniteAuxEmbedding_apply
    (f : Nat → Nat) (hf : FiniteAuxEmbedding H K f m)
    (i : Fin m) :
    (ofFiniteAuxEmbedding f hf).image i = f i.val := rfl

/-- Restrict a globally aux-type-respecting induced embedding to
the genuine finite source. No claim is made that the arbitrary
zero-extended tail is part of the finite colouring. -/
def ofAuxTypeRespectingEmbedding
    (e : Embedding H K) (he : e.AuxTypeRespecting) :
    FiniteAuxEmbeddingImage H K m :=
  ofFiniteAuxEmbedding e.toFun {
    strictMono := e.strictMono
    edge_iff := by
      intro a b c hab hbc hc
      exact e.edge_iff hab hbc
    one := by
      intro l u v hlu hlv hu hv
      exact he.one l u v hlu hlv
    aux := by
      intro l a b c d hla hab hlc hcd hb hd
      exact he.aux l a b c d hla hab hlc hcd
  }

@[simp] theorem ofAuxTypeRespectingEmbedding_apply
    (e : Embedding H K) (he : e.AuxTypeRespecting)
    (i : Fin m) :
    (ofAuxTypeRespectingEmbedding e he).image i = e i.val := rfl

/-- Equality of restricted full embeddings depends only on the
m genuine vertices, even if their infinitely zero-extended maps
differ everywhere above m. -/
theorem ofAuxTypeRespectingEmbedding_eq
    (e d : Embedding H K)
    (he : e.AuxTypeRespecting) (hd : d.AuxTypeRespecting)
    (h : ∀ i : Fin m, e i.val = d i.val) :
    ofAuxTypeRespectingEmbedding (m := m) e he =
      ofAuxTypeRespectingEmbedding (m := m) d hd := by
  ext i
  exact h i

end FiniteAuxEmbeddingImage
end Ordered3Graph
end ThreeUniformDiaries
