import ThreeUniformDiaries.DiaryUnorderedNativeStabilisation

/-!
# Transferring I2 through a gappy type-respecting source embedding

The pre-embedding proof first chooses a type-respecting embedding
ψ:D→G of the source diary into the generic hypergraph, then applies
the fused generic self-embedding and an initially UNORDERED target
embedding F. The already verified native I2 conclusion is stated
at cuts in G. The diary proof needs it at cuts indexed by D.

Since ψ may skip indices, the predecessor ψ(i−1) need not equal
ψ(i)−1. The actual native I2 target cut is
Φ(ψ(i)−1)+1, which is AT LEAST Φ(ψ(i−1))+1 for the ordered
stabilised target embedding Φ=F∘g. Restriction to the smaller
cut gives precisely the diary-level I2 condition.

This module proves both the arbitrary positive-cut transfer and
its specialisation to the successor cut i+1, used for witness
independence at a diary split. No convexity or consecutive-image
assumption on ψ is made.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace UnorderedEmbedding

/-- The fused native I2 theorem transfers through any gappy
type-respecting source copy, at the image of the PREDECESSOR
source vertex rather than at an incorrectly assumed consecutive
target level. -/
theorem stabilisedOrdered_oneType_of_source
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i u v : Nat) (hi : 0 < i)
    (hiu : i ≤ u) (hiv : i ≤ v)
    (hSame : H.SameOneTypeBelow i u v) :
    K.SameOneTypeBelow
      (stabilisedOrdered G K F (ψ (i-1)) + 1)
      (stabilisedOrdered G K F (ψ u))
      (stabilisedOrdered G K F (ψ v)) := by
  let Φ := stabilisedOrdered G K F
  have hG : G.graph.SameOneTypeBelow (ψ i) (ψ u) (ψ v) :=
    (hψ.one i u v hiu hiv).mp hSame
  have hpre : i-1 < i := by omega
  have hψpre : ψ (i-1) < ψ i := ψ.strictMono hpre
  have hpositive : 0 < ψ i := by omega
  have hI2 : K.SameOneTypeBelow (Φ (ψ i-1) + 1)
      (Φ (ψ u)) (Φ (ψ v)) :=
    stabilisedOrdered_singletonTypes G K F
      (ψ i) hpositive (ψ u) (ψ v)
      (ψ.strictMono.monotone hiu)
      (ψ.strictMono.monotone hiv) hG
  have hψpred : ψ (i-1) ≤ ψ i-1 := by omega
  have hcut :
      Φ (ψ (i-1)) + 1 ≤ Φ (ψ i-1) + 1 := by
    have hmono : Φ (ψ (i-1)) ≤ Φ (ψ i-1) :=
      Φ.strictMono.monotone hψpred
    omega
  intro x y hxy hy
  exact hI2 (a := x) (b := y) hxy (by omega)

/-- In particular equal singleton types through a successor
diary cut i+1 remain equal below the precise image cut Φ(ψi)+1,
independently of any gaps in ψ's enumeration. -/
theorem stabilisedOrdered_oneType_of_source_succ
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i u v : Nat)
    (hiu : i+1 ≤ u) (hiv : i+1 ≤ v)
    (hSame : H.SameOneTypeBelow (i+1) u v) :
    K.SameOneTypeBelow
      (stabilisedOrdered G K F (ψ i) + 1)
      (stabilisedOrdered G K F (ψ u))
      (stabilisedOrdered G K F (ψ v)) := by
  have h := stabilisedOrdered_oneType_of_source
    G K F ψ hψ (i+1) u v
    (by omega) hiu hiv hSame
  have hprev : i+1-1 = i := by omega
  simpa only [hprev] using h

end UnorderedEmbedding
end Ordered3Graph
end ThreeUniformDiaries
