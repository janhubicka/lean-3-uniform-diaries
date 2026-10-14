import ThreeUniformDiaries.DiaryFinitePointedATRCode
import ThreeUniformDiaries.InfinitePrefixes
import ThreeUniformDiaries.TypeRepresentation

/-!
# Finite pointed diary envelopes as native EnumNode Ramsey sources

The checked finite ATR theorem colours an `EnumNode m` source,
represented on Nat by a ZERO extension. Our pointed envelope is the
first m vertices of an induced hypergraph whose continuation need
not be zero. Their types at cuts involving only actual finite
vertices nevertheless agree exactly.

We prove the explicit first-m-vertices transfer for singleton and
auxiliary types, then build a `FiniteAuxEmbeddingImage` of the
actual `EnumNode m` source. No synthetic assumption on any source
or target tail appears in the final colouring code.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Restricting an enumerated hypergraph to its first m vertices
does not change singleton-type agreements involving vertices below m
at cuts no later than either endpoint. -/
theorem initialSegment_oneType_iff
    (H : Ordered3Graph Nat) (m w u v : Nat)
    (hwu : w ≤ u) (hwv : w ≤ v)
    (hu : u < m) (hv : v < m) :
    ((H.initialSegment m).toOrdered3Graph).SameOneTypeBelow w u v ↔
      H.SameOneTypeBelow w u v := by
  constructor
  · intro hsource x y hxy hyw
    have hyu : y < u := lt_of_lt_of_le hyw hwu
    have hyv : y < v := lt_of_lt_of_le hyw hwv
    exact (H.initialSegment_edge_iff hxy hyu hu).symm.trans
      ((hsource hxy hyw).trans
        (H.initialSegment_edge_iff hxy hyv hv))
  · intro hsource x y hxy hyw
    have hyu : y < u := lt_of_lt_of_le hyw hwu
    have hyv : y < v := lt_of_lt_of_le hyw hwv
    exact (H.initialSegment_edge_iff hxy hyu hu).trans
      ((hsource hxy hyw).trans
        (H.initialSegment_edge_iff hxy hyv hv).symm)

/-- The same exact finite restriction property for the auxiliary
2-type of two ordered pairs of vertices below m. -/
theorem initialSegment_auxType_iff
    (H : Ordered3Graph Nat) (m w u v x y : Nat)
    (hwu : w ≤ u) (huv : u < v)
    (hwx : w ≤ x) (hxy : x < y)
    (hv : v < m) (hy : y < m) :
    ((H.initialSegment m).toOrdered3Graph).SameAuxTypeBelow w u v x y ↔
      H.SameAuxTypeBelow w u v x y := by
  constructor
  · intro hsource z hzw
    have hzu : z < u := lt_of_lt_of_le hzw hwu
    have hzx : z < x := lt_of_lt_of_le hzw hwx
    exact (H.initialSegment_edge_iff hzu huv hv).symm.trans
      ((hsource hzw).trans
        (H.initialSegment_edge_iff hzx hxy hy))
  · intro hsource z hzw
    have hzu : z < u := lt_of_lt_of_le hzw hwu
    have hzx : z < x := lt_of_lt_of_le hzw hwx
    exact (H.initialSegment_edge_iff hzu huv hv).trans
      ((hsource hzw).trans
        (H.initialSegment_edge_iff hzx hxy hy).symm)

namespace FiniteAuxEmbedding

/-- Replace the potentially nonzero infinite continuation of the
finite source by the canonical zero-extended EnumNode. The finite
aux-embedding constraints are unchanged. -/
theorem of_initialSegment
    {H K : Ordered3Graph Nat} {f : Nat → Nat} {m : Nat}
    (hf : FiniteAuxEmbedding H K f m) :
    FiniteAuxEmbedding (H.initialSegment m).toOrdered3Graph K f m := by
  refine {
    strictMono := hf.strictMono
    edge_iff := ?_
    one := ?_
    aux := ?_
  }
  · intro a b c hab hbc hc
    exact (H.initialSegment_edge_iff hab hbc hc).trans
      (hf.edge_iff a b c hab hbc hc)
  · intro w u v hwu hwv hu hv
    exact (H.initialSegment_oneType_iff m w u v hwu hwv hu hv).trans
      (hf.one w u v hwu hwv hu hv)
  · intro w u v x y hwu huv hwx hxy hv hy
    exact (H.initialSegment_auxType_iff
      m w u v x y hwu huv hwx hxy hv hy).trans
      (hf.aux w u v x y hwu huv hwx hxy hv hy)

end FiniteAuxEmbedding

namespace FinitePointedEnvelope

variable {K : Ordered3Graph Nat} {j a b : Nat}

/-- The genuine finite enumerated hypergraph to be coloured by ATR. -/
noncomputable def finiteEnum (E : FinitePointedEnvelope K j a b) :
    EnumNode E.size :=
  E.induced.initialSegment E.size

/-- The canonical pointed envelope inclusion as a finite ATR
embedding image with exactly the `size` true source vertices. -/
noncomputable def finiteATRCode
    (E : FinitePointedEnvelope K j a b) :
    FiniteAuxEmbeddingImage E.finiteEnum.toOrdered3Graph K E.size :=
  FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding E.enumerate
    E.finite_aux_embedding.of_initialSegment

theorem finiteATRCode_fix_prefix
    (E : FinitePointedEnvelope K j a b)
    (t : Fin E.size) (ht : t.val < j) :
    E.finiteATRCode.image t = t.val := by
  change E.enumerate t.val = t.val
  exact E.protected_prefix t.val ht

theorem finiteATRCode_final_endpoints
    (E : FinitePointedEnvelope K j a b) :
    E.finiteATRCode.image
        ⟨E.size - 2, by have h := E.size_lower; omega⟩ = a ∧
      E.finiteATRCode.image
        ⟨E.size - 1, by have h := E.size_lower; omega⟩ = b := by
  constructor
  · change E.enumerate (E.size - 2) = a
    exact E.first_endpoint
  · change E.enumerate (E.size - 1) = b
    exact E.second_endpoint

end FinitePointedEnvelope
end Ordered3Graph
end ThreeUniformDiaries
