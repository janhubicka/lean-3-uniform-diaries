import ThreeUniformDiaries.DiaryFiniteLeafMeetPrefixCompression
import ThreeUniformDiaries.DiaryFiniteLeafMeetMarkerReindex

/-!
# V1 and V2 coherence under arbitrary finite induced compression

For a genuine source RoleDiary, every selected split-positive
class has equal source singleton or full ordered-pair types below
the old split level. Deleting other source vertices cannot destroy
this equality: the verified forward finite-support prefix
transport directly gives the required target type equality.

This is true for ANY finite support containing markers 0,1,2,
not only the special leaf-meet support. Source split roles and
positive incidences are reflected literally by inducedness.
All relevant split and leaf vertices lie inside the finite
range because each positive edge is in the induced finite table.

The proofs quantify over EVERY actual positive leaf or ordered
pair in the target. They do not assume S1/S2 for the compressed
graph, and do not assert split-witness existence.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {S : Finset Nat}

/-- Original V1 positive-class coherence survives arbitrary
increasing induced compression retaining all three markers. -/
theorem finiteSupportGraph_oneSplit_coherent
    (D : RoleDiary G)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (k i j : Nat)
    (hSplit : IsOneSplit (finiteSupportGraph G S) k)
    (hiLeaf : IsLeaf (finiteSupportGraph G S) i)
    (hjLeaf : IsLeaf (finiteSupportGraph G S) j)
    (hA : (finiteSupportGraph G S).edge 0 k i)
    (hB : (finiteSupportGraph G S).edge 0 k j) :
    (finiteSupportGraph G S).SameOneTypeBelow k i j := by
  have hk3 : 3 ≤ k := hSplit.1
  have hi3 : 3 ≤ i := hiLeaf.1
  have hj3 : 3 ≤ j := hjLeaf.1
  have hOrderedA := finiteSupportGraph_edge_ordered G S 0 k i hA
  have hOrderedB := finiteSupportGraph_edge_ordered G S 0 k j hB
  have hk : k < S.card := by omega
  have hi : i < S.card := hOrderedA.2.2.2
  have hj : j < S.card := hOrderedB.2.2.2
  have hki : k < i := hOrderedA.2.1
  have hkj : k < j := hOrderedB.2.1
  have hSourceSplit : IsOneSplit G (finiteSupportIndex S k) :=
    (finiteSupportGraph_oneSplit_iff
      (G := G) (S := S) h0 h1 h2 k hk3 hk).mp hSplit
  have hSourceLeafI : IsLeaf G (finiteSupportIndex S i) :=
    (finiteSupportGraph_leaf_iff
      (G := G) (S := S) h0 h1 h2 i hi3 hi).mp hiLeaf
  have hSourceLeafJ : IsLeaf G (finiteSupportIndex S j) :=
    (finiteSupportGraph_leaf_iff
      (G := G) (S := S) h0 h1 h2 j hj3 hj).mp hjLeaf
  obtain ⟨_hCard,hZero,_hOne,_hTwo⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  have hSourceEdgeI :
      G.edge 0 (finiteSupportIndex S k) (finiteSupportIndex S i) := by
    have h := (finiteSupportGraph_edge_iff G S 0 k i
      (by omega) hki hi).mp hA
    simpa only [hZero] using h
  have hSourceEdgeJ :
      G.edge 0 (finiteSupportIndex S k) (finiteSupportIndex S j) := by
    have h := (finiteSupportGraph_edge_iff G S 0 k j
      (by omega) hkj hj).mp hB
    simpa only [hZero] using h
  have hSourceAgreement := D.one_split_coherent
    (finiteSupportIndex S k)
    (finiteSupportIndex S i) (finiteSupportIndex S j)
    hSourceSplit hSourceLeafI hSourceLeafJ
    hSourceEdgeI hSourceEdgeJ
  exact finiteSupportGraph_oneType_of_original
    (G := G) (S := S) k i j hk hi hj
    hki.le hkj.le hSourceAgreement

/-- Original V2 positive-class coherence likewise survives
arbitrary finite induced compression, including comparisons of
all actual positive ordered leaf pairs in the target. -/
theorem finiteSupportGraph_twoSplit_coherent
    (D : RoleDiary G)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (k i j p q : Nat)
    (hSplit : IsTwoSplit (finiteSupportGraph G S) k)
    (hij : i < j) (hpq : p < q)
    (hiLeaf : IsLeaf (finiteSupportGraph G S) i)
    (hjLeaf : IsLeaf (finiteSupportGraph G S) j)
    (hpLeaf : IsLeaf (finiteSupportGraph G S) p)
    (hqLeaf : IsLeaf (finiteSupportGraph G S) q)
    (hAB : (finiteSupportGraph G S).edge k i j)
    (hCD : (finiteSupportGraph G S).edge k p q) :
    (finiteSupportGraph G S).SameTwoTypeBelow k i j p q := by
  have hk3 : 3 ≤ k := hSplit.1
  have hi3 : 3 ≤ i := hiLeaf.1
  have hj3 : 3 ≤ j := hjLeaf.1
  have hp3 : 3 ≤ p := hpLeaf.1
  have hq3 : 3 ≤ q := hqLeaf.1
  have hOrderedAB := finiteSupportGraph_edge_ordered G S k i j hAB
  have hOrderedCD := finiteSupportGraph_edge_ordered G S k p q hCD
  have hk : k < S.card := by omega
  have hi : i < S.card := by omega
  have hj : j < S.card := hOrderedAB.2.2.2
  have hp : p < S.card := by omega
  have hq : q < S.card := hOrderedCD.2.2.2
  have hki : k < i := hOrderedAB.1
  have hkp : k < p := hOrderedCD.1
  have hSourceSplit : IsTwoSplit G (finiteSupportIndex S k) :=
    (finiteSupportGraph_twoSplit_iff
      (G := G) (S := S) h0 h1 h2 k hk3 hk).mp hSplit
  have hSourceLeafI : IsLeaf G (finiteSupportIndex S i) :=
    (finiteSupportGraph_leaf_iff
      (G := G) (S := S) h0 h1 h2 i hi3 hi).mp hiLeaf
  have hSourceLeafJ : IsLeaf G (finiteSupportIndex S j) :=
    (finiteSupportGraph_leaf_iff
      (G := G) (S := S) h0 h1 h2 j hj3 hj).mp hjLeaf
  have hSourceLeafP : IsLeaf G (finiteSupportIndex S p) :=
    (finiteSupportGraph_leaf_iff
      (G := G) (S := S) h0 h1 h2 p hp3 hp).mp hpLeaf
  have hSourceLeafQ : IsLeaf G (finiteSupportIndex S q) :=
    (finiteSupportGraph_leaf_iff
      (G := G) (S := S) h0 h1 h2 q hq3 hq).mp hqLeaf
  have hSourceOrderAB :=
    finiteSupportIndex_strictMono S i j hij hj
  have hSourceOrderCD :=
    finiteSupportIndex_strictMono S p q hpq hq
  have hSourceEdgeAB :
      G.edge (finiteSupportIndex S k)
        (finiteSupportIndex S i) (finiteSupportIndex S j) :=
    (finiteSupportGraph_edge_iff G S k i j hki hij hj).mp hAB
  have hSourceEdgeCD :
      G.edge (finiteSupportIndex S k)
        (finiteSupportIndex S p) (finiteSupportIndex S q) :=
    (finiteSupportGraph_edge_iff G S k p q hkp hpq hq).mp hCD
  have hSourceAgreement := D.two_split_coherent
    (finiteSupportIndex S k)
    (finiteSupportIndex S i) (finiteSupportIndex S j)
    (finiteSupportIndex S p) (finiteSupportIndex S q)
    hSourceSplit hSourceOrderAB hSourceOrderCD
    hSourceLeafI hSourceLeafJ hSourceLeafP hSourceLeafQ
    hSourceEdgeAB hSourceEdgeCD
  exact finiteSupportGraph_twoType_of_original
    (G := G) (S := S) k i j p q
    hk hi hj hp hq hij hpq hki.le hkp.le hSourceAgreement

end DiaryLeafPriority
end ThreeUniformDiaries
