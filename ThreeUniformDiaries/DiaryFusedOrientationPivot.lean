import ThreeUniformDiaries.DiaryGappySourceI2Transfer
import ThreeUniformDiaries.DiaryGappySourceI3TwoSplit
import ThreeUniformDiaries.DiaryUnorderedNativeStabilisation
import ThreeUniformDiaries.DiaryOrientationReplacement
import ThreeUniformDiaries.DiaryEdgeShapeWitness

/-!
# General orientation pivot under the genuinely fused lower-bound map

The five-vertex gadget's elementary mechanism does not depend on
the literal vertices 0,1,2,3,4 or their single-edge pattern.

Suppose a source singleton meet is m = x∧y, strictly before x
and y, and a third vertex z has the SAME singleton type as x
through m+1. Then for any type-respecting, possibly gappy
source embedding into the generic hypergraph and any initially
UNORDERED outer hypergraph embedding, the verified fused
ordered target map sends the comparisons (x,y) and (z,y)
to the SAME lexicographic orientation.

Proof:
* The actual source singleton meet supplies a first-disagreement
  edge (t,m,x) versus (t,m,y), with t<m.
* The induced ordered target embedding preserves and reflects
  these two edge bits, so its target singleton meet of (x,y)
  is at most the image of m. This requires no type-preserving
  assumption on omitted target levels.
* The verified gappy-source I2 successor-cut transfer sends
  the source equality of 1-types of x,z through m+1 to their
  target equality through the image of m plus one.
* The elementary checked earlier-meet orientation replacement
  lemma then gives the desired lexicographic equality.

No diary roles, generic envelope equality, global orientation
synchronisation or artificial target meet preservation are
assumed. This is the reusable arbitrary-configuration pivot
behind the local five-vertex orientation proof.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace UnorderedEmbedding

/-- Exact orientation pivot through an arbitrary gappy
type-respecting source copy, under the ACTUAL fused unordered
outer hypergraph embedding. The target relation is induced and
order-preserving only AFTER fusion, not beforehand. -/
theorem stabilisedSource_lexEarlier_pivot
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (m x y z : Nat)
    (hmx : m < x) (hmy : m < y) (hmz : m < z)
    (hmeet : H.oneMeetLevel x y = m)
    (hSame : H.SameOneTypeBelow (m+1) x z) :
    let φ := stabilisedSource G K F ψ
    DiaryLeafPriority.LexEarlier K (φ x) (φ y) ↔
      DiaryLeafPriority.LexEarlier K (φ z) (φ y) := by
  let φ := stabilisedSource G K F ψ
  have hclose : K.SameOneTypeBelow (φ m + 1) (φ x) (φ z) :=
    stabilisedOrdered_oneType_of_source_succ
      G K F ψ hψ m x z (by omega) (by omega) hSame
  obtain ⟨t, htm, hdiff⟩ :=
    DiaryLeafPriority.oneMeetLevel_has_first_witness
      H x y m hmeet hmx hmy
  have htargetDiff :
      ¬ (K.edge (φ t) (φ m) (φ x) ↔
         K.edge (φ t) (φ m) (φ y)) := by
    intro hEq
    have hx : H.edge t m x ↔ K.edge (φ t) (φ m) (φ x) :=
      φ.edge_iff htm hmx
    have hy : H.edge t m y ↔ K.edge (φ t) (φ m) (φ y) :=
      φ.edge_iff htm hmy
    exact hdiff (hx.trans (hEq.trans hy.symm))
  have htargetMeet :
      K.oneMeetLevel (φ x) (φ y) ≤ φ m :=
    K.oneMeetLevel_le_of_edge_disagreement
      (φ x) (φ y) (φ t) (φ m)
      (φ.strictMono htm) htargetDiff
  exact K.lexEarlier_stable_under_close_one_types
    (φ m) (φ x) (φ y) (φ z)
    (φ.strictMono hmx) (φ.strictMono hmy) (φ.strictMono hmz)
    hclose htargetMeet

end UnorderedEmbedding
end Ordered3Graph
end ThreeUniformDiaries
