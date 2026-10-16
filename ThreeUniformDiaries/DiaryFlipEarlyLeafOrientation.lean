import ThreeUniformDiaries.DiaryPrediaryDefinition

/-!
# Earlier-leaf orientation constraints on positive split classes

The revised flip-node sharing argument cannot be justified by checking
only the original branch's positive type profile. In the ambient
pre-diary, every earlier leaf outside a chosen branch also supplies
Devlin-marker singleton tests on later positively incident leaves.

The V1/V2 axioms FORCE these marker bits to agree. We extract the exact
necessary consequence: a positive 1-split class is never separated
by an earlier leaf in the lexicographic order; positive pairs at a
2-split have the same earlier-leaf lex orientation in EACH component.

This is a global obstruction on any cross-branch marker assignment.
It does not construct such an assignment or finish flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RolePrediary

variable {H : Ordered3Graph Nat}

/-- Every original leaf u preceding a positive 1-split sees the
same Devlin orientation towards any two positive incident leaves.
This follows from V1 singleton-type coherence and V3. -/
theorem positive_oneSplit_early_leaf_lex_agrees
    (P : RolePrediary H)
    (m u a b : Nat)
    (hm : IsOneSplit H m)
    (hu : IsLeaf H u) (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hum : u < m)
    (hposA : H.edge 0 m a) (hposB : H.edge 0 m b) :
    (LexEarlier H u a ↔ LexEarlier H u b) := by
  have hma : m < a := (P.edge_ordered 0 m a hposA).2
  have hmb : m < b := (P.edge_ordered 0 m b hposB).2
  have hua : u < a := lt_trans hum hma
  have hub : u < b := lt_trans hum hmb
  have hu1 : 1 < u := by have h3 := hu.1; omega
  have hsame := P.one_split_coherent m a b hm ha hb hposA hposB
  have htest : (H.edge 1 u a ↔ H.edge 1 u b) :=
    hsame hu1 hum
  exact (P.leaf_marker_one u a hua hu ha).symm.trans
    (htest.trans (P.leaf_marker_one u b hub hu hb))

/-- The analogue for two positively incident ordered leaf pairs:
any earlier leaf sees the same lex ordering toward each
corresponding coordinate. Reversing one of the cross-marker
bits would violate V2 even when all branch edges are induced. -/
theorem positive_twoSplit_early_leaf_lex_agrees
    (P : RolePrediary H)
    (m u a b c d : Nat)
    (hm : IsTwoSplit H m)
    (hu : IsLeaf H u)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hum : u < m)
    (hab : a < b) (hcd : c < d)
    (hposAB : H.edge m a b) (hposCD : H.edge m c d) :
    (LexEarlier H u a ↔ LexEarlier H u c) ∧
    (LexEarlier H u b ↔ LexEarlier H u d) := by
  have hma : m < a := (P.edge_ordered m a b hposAB).1
  have hmc : m < c := (P.edge_ordered m c d hposCD).1
  have hub : u < b := lt_trans (lt_trans hum hma) hab
  have hud : u < d := lt_trans (lt_trans hum hmc) hcd
  have hua : u < a := lt_trans hum hma
  have huc : u < c := lt_trans hum hmc
  have hu1 : 1 < u := by have h3 := hu.1; omega
  have htypes := P.two_split_coherent m a b c d hm hab hcd
      ha hb hc hd hposAB hposCD
  have h0 : (H.edge 1 u a ↔ H.edge 1 u c) :=
    htypes.1 hu1 hum
  have h1 : (H.edge 1 u b ↔ H.edge 1 u d) :=
    htypes.2.1 hu1 hum
  constructor
  · exact (P.leaf_marker_one u a hua hu ha).symm.trans
      (h0.trans (P.leaf_marker_one u c huc hu hc))
  · exact (P.leaf_marker_one u b hub hu hb).symm.trans
      (h1.trans (P.leaf_marker_one u d hud hu hd))

end RolePrediary
end DiaryLeafPriority
end ThreeUniformDiaries
