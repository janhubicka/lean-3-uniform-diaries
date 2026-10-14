import ThreeUniformDiaries.DiaryFinitePointedEnumNode
import ThreeUniformDiaries.ActualFiniteAuxRamseyAll

/-!
# Apply the unconditional finite ATR theorem to pointed diary envelopes

The verified finite ATR theorem is formulated for `EnumNode (k+1)`.
Pointed diary envelopes have finite size m >= j+2, which is
positive but need not appear syntactically as k+1. We first remove
that accidental API mismatch without adding mathematical assumptions.

The resulting application colours the genuine `Fin m` images of
an actual finite pointed envelope. It obtains ONE global
aux-type-respecting self-embedding of the generic 3-hypergraph
fixing the protected prefix, and a constant colour on all
protected-prefix finite copies of the same enumerated envelope.

This is the precise single-envelope stabilisation input. Iteration
over finitely many singleton and pair-envelope shapes and
countable fusion remain separate proof obligations.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

/-- Unconditional finite ATR with an arbitrary positive source size,
rather than the particular notation k+1. -/
theorem actualFiniteAuxRamsey_positiveSize
    (G : GenericEnumerated3Graph)
    {n m : Nat} (hnm : n ≤ m) (hm : 0 < m)
    (A : EnumNode m)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G.graph m → κ) :
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
        (∀ j < n, u j = j) ∧
        ∃ color : κ,
          ∀ e : Ordered3Graph.FiniteAuxEmbeddingImage
              A.toOrdered3Graph G.graph m,
            (∀ i : Fin m, i.val < n → e.image i = i.val) →
            χ (e.postcompose u hu) = color := by
  cases m with
  | zero =>
      omega
  | succ k =>
      exact actualFiniteAuxRamsey_allFinite G (n := n) (k := k)
        hnm A χ

end ATRFiniteDecoder

namespace Ordered3Graph
namespace FinitePointedEnvelope

/-- Ramsey homogeneity for all finite aux-type-respecting copies
of the canonical pointed envelope fixing the protected full prefix.
No infinite-zero-tail embeddings are ever coloured. -/
theorem ramsey_for_fixed_prefix
    (G : GenericEnumerated3Graph)
    {j a b : Nat} (E : FinitePointedEnvelope G.graph j a b)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : FiniteAuxEmbeddingImage E.finiteEnum.toOrdered3Graph
      G.graph E.size → κ) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
        (∀ t < j, u t = t) ∧
        ∃ color : κ,
          ∀ e : FiniteAuxEmbeddingImage
              E.finiteEnum.toOrdered3Graph G.graph E.size,
            (∀ i : Fin E.size, i.val < j → e.image i = i.val) →
            χ (e.postcompose u hu) = color := by
  have hpos : 0 < E.size := by
    have hlower := E.size_lower
    omega
  have hbound : j ≤ E.size := by
    have hlower := E.size_lower
    omega
  exact ATRFiniteDecoder.actualFiniteAuxRamsey_positiveSize
    G (n := j) (m := E.size)
    hbound hpos E.finiteEnum χ

/-- In particular, the homogenising colour is attained by the
canonical finite pointed-envelope inclusion itself, after the
Ramsey self-embedding. -/
theorem ramsey_colour_on_canonical_copy
    (G : GenericEnumerated3Graph)
    {j a b : Nat} (E : FinitePointedEnvelope G.graph j a b)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : FiniteAuxEmbeddingImage E.finiteEnum.toOrdered3Graph
      G.graph E.size → κ) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
        (∀ t < j, u t = t) ∧
        ∃ color : κ,
          χ (E.finiteATRCode.postcompose u hu) = color ∧
          ∀ e : FiniteAuxEmbeddingImage
              E.finiteEnum.toOrdered3Graph G.graph E.size,
            (∀ i : Fin E.size, i.val < j → e.image i = i.val) →
            χ (e.postcompose u hu) = color := by
  obtain ⟨u, hu, hfix, color, hcol⟩ :=
    E.ramsey_for_fixed_prefix G χ
  refine ⟨u, hu, hfix, color, ?_, hcol⟩
  exact hcol E.finiteATRCode E.finiteATRCode_fix_prefix

end FinitePointedEnvelope
end Ordered3Graph
end ThreeUniformDiaries
