import ThreeUniformDiaries.ActualFiniteEmbeddingMeets
import ThreeUniformDiaries.InfinitePrefixes
import ThreeUniformDiaries.TypeRepresentation

/-!
# A genuine finite aux-embedding only needs a finite target prefix

In manuscript Aemb, H may be any countable enumerated hypergraph,
whereas the type-tree pictures in the current Lean files are built
from a finite EnumNode N. This module bridges that difference.

Choose N larger than the largest selected image f(m-1). Every source
edge and every target type test involving a genuine source vertex
lies below N, so the embedding and all finite selected-cut
one/aux comparisons are preserved by restricting H to H|N.
There is no zero-extension requirement on the original target.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace FiniteAuxEmbedding

/-- Restrict the target of a finite aux-type-respecting embedding
to an initial segment containing every actual selected image. -/
theorem target_initialSegment
    {m : Nat} (A : EnumNode m) (G : Ordered3Graph Nat)
    (f : Nat → Nat)
    (hf : FiniteAuxEmbedding A.toOrdered3Graph G f m)
    (hm : 0 < m) (N : Nat) (hN : f (m - 1) < N) :
    FiniteAuxEmbedding A.toOrdered3Graph
      (G.initialSegment N).toOrdered3Graph f m := by
  let K := (G.initialSegment N).toOrdered3Graph
  have hbound : ∀ t : Nat, t < m → f t < N := by
    intro t ht
    have hlast : t ≤ m - 1 := by omega
    exact lt_of_le_of_lt (hf.strictMono.monotone hlast) hN
  refine ⟨hf.strictMono, ?_, ?_, ?_⟩
  · intro a b c hab hbc hc
    have hcN : f c < N := hbound c hc
    have hca : f a < f b := hf.strictMono hab
    have hcb : f b < f c := hf.strictMono hbc
    exact (hf.edge_iff a b c hab hbc hc).trans
      (G.initialSegment_edge_iff hca hcb hcN).symm
  · intro w u v hwu hwv hu hv
    have huN : f u < N := hbound u hu
    have hvN : f v < N := hbound v hv
    have hcut : G.SameOneTypeBelow (f w) (f u) (f v) ↔
        K.SameOneTypeBelow (f w) (f u) (f v) := by
      constructor
      · intro h a b hab hb
        have hbu : b < f u :=
          lt_of_lt_of_le hb (hf.strictMono.monotone hwu)
        have hbv : b < f v :=
          lt_of_lt_of_le hb (hf.strictMono.monotone hwv)
        calc
          K.edge a b (f u) ↔ G.edge a b (f u) :=
            G.initialSegment_edge_iff hab hbu huN
          _ ↔ G.edge a b (f v) := h hab hb
          _ ↔ K.edge a b (f v) :=
            (G.initialSegment_edge_iff hab hbv hvN).symm
      · intro h a b hab hb
        have hbu : b < f u :=
          lt_of_lt_of_le hb (hf.strictMono.monotone hwu)
        have hbv : b < f v :=
          lt_of_lt_of_le hb (hf.strictMono.monotone hwv)
        calc
          G.edge a b (f u) ↔ K.edge a b (f u) :=
            (G.initialSegment_edge_iff hab hbu huN).symm
          _ ↔ K.edge a b (f v) := h hab hb
          _ ↔ G.edge a b (f v) :=
            G.initialSegment_edge_iff hab hbv hvN
    exact (hf.one w u v hwu hwv hu hv).trans hcut
  · intro w u₀ u₁ v₀ v₁ hwu hu hwv hv hu₁ hv₁
    have huN : f u₁ < N := hbound u₁ hu₁
    have hvN : f v₁ < N := hbound v₁ hv₁
    have hcut : G.SameAuxTypeBelow (f w)
        (f u₀) (f u₁) (f v₀) (f v₁) ↔
        K.SameAuxTypeBelow (f w)
          (f u₀) (f u₁) (f v₀) (f v₁) := by
      constructor
      · intro h a ha
        have hau : a < f u₀ :=
          lt_of_lt_of_le ha (hf.strictMono.monotone hwu)
        have hav : a < f v₀ :=
          lt_of_lt_of_le ha (hf.strictMono.monotone hwv)
        calc
          K.edge a (f u₀) (f u₁) ↔ G.edge a (f u₀) (f u₁) :=
            G.initialSegment_edge_iff hau (hf.strictMono hu) huN
          _ ↔ G.edge a (f v₀) (f v₁) := h ha
          _ ↔ K.edge a (f v₀) (f v₁) :=
            (G.initialSegment_edge_iff hav (hf.strictMono hv) hvN).symm
      · intro h a ha
        have hau : a < f u₀ :=
          lt_of_lt_of_le ha (hf.strictMono.monotone hwu)
        have hav : a < f v₀ :=
          lt_of_lt_of_le ha (hf.strictMono.monotone hwv)
        calc
          G.edge a (f u₀) (f u₁) ↔ K.edge a (f u₀) (f u₁) :=
            (G.initialSegment_edge_iff hau (hf.strictMono hu) huN).symm
          _ ↔ K.edge a (f v₀) (f v₁) := h ha
          _ ↔ G.edge a (f v₀) (f v₁) :=
            G.initialSegment_edge_iff hav (hf.strictMono hv) hvN
    exact (hf.aux w u₀ u₁ v₀ v₁ hwu hu hwv hv hu₁ hv₁).trans hcut

end FiniteAuxEmbedding
end Ordered3Graph
end ThreeUniformDiaries
