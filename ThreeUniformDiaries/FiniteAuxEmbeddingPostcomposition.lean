import ThreeUniformDiaries.FiniteAuxEmbeddingImage
import ThreeUniformDiaries.AuxTypeRespectingComposition

/-!
# Actual postcomposition action on finite ATR embedding colours

The Ramsey conclusion colours finite embeddings of A into G.
An ambient aux-type-respecting self-embedding acts on such a colour
by postcomposing the images of the actual m source vertices.
There is NO action on a fictitious infinite tail of the zero-extended
A, and no stronger global finite-source preservation assumption.

The proof first establishes stability of the genuinely finite
FiniteAuxEmbedding condition under postcomposition with any global
aux-type-respecting induced embedding, then descends the action to
the extensional Fin m colour domain. Its application and composition
laws are literal equalities of those m images.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

namespace FiniteAuxEmbedding

variable {H K L : Ordered3Graph Nat}
variable {f : Nat → Nat} {m : Nat}

/-- The finite aux-type-respecting embedding property is stable
under composition with a genuine ambient aux embedding, without
imposing conditions on any out-of-range source vertices. -/
theorem postcompose
    (hf : FiniteAuxEmbedding H K f m)
    (g : Embedding K L) (hg : g.AuxTypeRespecting) :
    FiniteAuxEmbedding H L (fun i => g (f i)) m := by
  refine ⟨g.strictMono.comp hf.strictMono, ?_, ?_, ?_⟩
  · intro a b c hab hbc hc
    exact (hf.edge_iff a b c hab hbc hc).trans
      (g.edge_iff (hf.strictMono hab) (hf.strictMono hbc))
  · intro l u v hlu hlv hu hv
    exact (hf.one l u v hlu hlv hu hv).trans
      (hg.one (f l) (f u) (f v)
        (hf.strictMono.monotone hlu)
        (hf.strictMono.monotone hlv))
  · intro l a b c d hla hab hlc hcd hb hd
    exact (hf.aux l a b c d hla hab hlc hcd hb hd).trans
      (hg.aux (f l) (f a) (f b) (f c) (f d)
        (hf.strictMono.monotone hla)
        (hf.strictMono hab)
        (hf.strictMono.monotone hlc)
        (hf.strictMono hcd))

end FiniteAuxEmbedding

namespace FiniteAuxEmbeddingImage

variable {H K L M : Ordered3Graph Nat} {m : Nat}

/-- Postcompose the REAL finite m-vertex images; admissibility is
proved by extending any finite source witness and composing with g.
No choice of tail appears in the output data. -/
noncomputable def postcompose
    (c : FiniteAuxEmbeddingImage H K m)
    (g : Embedding K L) (hg : g.AuxTypeRespecting) :
    FiniteAuxEmbeddingImage H L m := by
  classical
  obtain ⟨f, hf, hc⟩ := c.admissible
  refine {
    image := fun i => g (c.image i)
    admissible := ⟨(fun j => g (f j)),
      hf.postcompose g hg, ?_⟩
  }
  intro i
  rw [hc i]

@[simp] theorem postcompose_apply
    (c : FiniteAuxEmbeddingImage H K m)
    (g : Embedding K L) (hg : g.AuxTypeRespecting)
    (i : Fin m) :
    (c.postcompose g hg).image i = g (c.image i) := rfl

/-- Postcomposition respects composition of ambient aux embeddings
EXACTLY on the finite source images, independently of any global
extension chosen to certify either finite map. -/
theorem postcompose_comp
    (c : FiniteAuxEmbeddingImage H K m)
    (g : Embedding K L) (hg : g.AuxTypeRespecting)
    (h : Embedding L M) (hh : h.AuxTypeRespecting) :
    (c.postcompose g hg).postcompose h hh =
      c.postcompose (h.comp g) (hh.comp hg) := by
  ext i
  rfl

end FiniteAuxEmbeddingImage
end Ordered3Graph
end ThreeUniformDiaries
