import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# The manuscript's actual pre-diary: exactly V/E, without S1/S2

Unlike the complete RoleDiary predicate, this intermediate
structure requires all role, split-witness, split-coherence,
Devlin leaf-marker and allowed-edge axioms, but DOES NOT
require the two diary meet axioms S1 and S2.

The essential fact for the capped 1-split insertion is proved
directly here: two distinct leaves a<b cannot agree as
singleton types through cut a+1. One of the V3 markers
distinguishes them, because hyperedges with a repeated
vertex are excluded by the increasing-edge axiom.

This requires no S1/S2 and is independent of the exact
new-edge insertion implementation.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Precisely the (V1,V2,V3,E) portion of the role-based
diary definition; S1/S2 have deliberately been omitted. -/
structure RolePrediary (H : Ordered3Graph Nat) : Prop where
  role_valid :
    ∀ v, 3 ≤ v → IsLeaf H v ∨ IsOneSplit H v ∨ IsTwoSplit H v
  one_split_coherent :
    ∀ m a b, IsOneSplit H m → IsLeaf H a → IsLeaf H b →
      H.edge 0 m a → H.edge 0 m b →
      H.SameOneTypeBelow m a b
  one_split_witness :
    ∀ m, IsOneSplit H m →
      ∃ a b, IsLeaf H a ∧ IsLeaf H b ∧
        m < a ∧ m < b ∧ H.oneMeetLevel a b = m
  two_split_coherent :
    ∀ m a b c d, IsTwoSplit H m →
      a < b → c < d →
      IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
      H.edge m a b → H.edge m c d →
      H.SameTwoTypeBelow m a b c d
  two_split_witness :
    ∀ m, IsTwoSplit H m →
      ∃ a b c d, a < b ∧ c < d ∧
        IsLeaf H a ∧ IsLeaf H b ∧ IsLeaf H c ∧ IsLeaf H d ∧
        m < a ∧ m < c ∧ H.twoMeetLevel a b c d = m
  leaf_marker_one :
    ∀ a b, a < b → IsLeaf H a → IsLeaf H b →
      (H.edge 1 a b ↔ LexEarlier H a b)
  leaf_marker_two :
    ∀ a b, a < b → IsLeaf H a → IsLeaf H b →
      (H.edge 2 a b ↔ ¬ LexEarlier H a b)
  edge_ordered :
    ∀ x y z, H.edge x y z → x < y ∧ y < z
  permitted_edge :
    ∀ x y z, H.edge x y z → PermittedDiaryEdge H x y z

namespace RoleDiary

variable {H : Ordered3Graph Nat}

/-- Forget only S1/S2, retaining the exact pre-diary conditions. -/
theorem toPrediary (D : RoleDiary H) : RolePrediary H where
  role_valid := D.role_valid
  one_split_coherent := D.one_split_coherent
  one_split_witness := D.one_split_witness
  two_split_coherent := D.two_split_coherent
  two_split_witness := D.two_split_witness
  leaf_marker_one := D.leaf_marker_one
  leaf_marker_two := D.leaf_marker_two
  edge_ordered := D.edge_ordered
  permitted_edge := D.permitted_edge

end RoleDiary

namespace RolePrediary

variable {H : Ordered3Graph Nat}

/-- Restoring S1/S2 yields exactly the original full RoleDiary. -/
theorem withMeets
    (P : RolePrediary H)
    (hOne : ∀ a b, IsLeaf H a → IsLeaf H b → a ≠ b →
      IsOneSplit H (H.oneMeetLevel a b))
    (hTwo : ∀ a b c d, a < b → c < d →
      IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
      H.twoMeetLevel a b c d = min a c ∨
      H.twoMeetLevel a b c d = 1 ∨
      IsTwoSplit H (H.twoMeetLevel a b c d)) :
    RoleDiary H where
  role_valid := P.role_valid
  one_split_coherent := P.one_split_coherent
  one_split_witness := P.one_split_witness
  two_split_coherent := P.two_split_coherent
  two_split_witness := P.two_split_witness
  leaf_marker_one := P.leaf_marker_one
  leaf_marker_two := P.leaf_marker_two
  edge_ordered := P.edge_ordered
  permitted_edge := P.permitted_edge
  singleton_meets := hOne
  pair_meets := hTwo

/-- Ordered 3-hypergraphs have no repeated-vertex edges. -/
theorem repeated_vertex_nonedge
    (P : RolePrediary H) (x y : Nat) : ¬ H.edge x y y := by
  intro he
  have horder := P.edge_ordered x y y he
  omega

/-- V3 already guarantees a Devlin marker on EVERY ordered
pair of leaves, without any S1/S2 assumptions. -/
theorem leaf_pair_has_marker
    (P : RolePrediary H) (a b : Nat) (hab : a < b)
    (ha : IsLeaf H a) (hb : IsLeaf H b) :
    H.edge 1 a b ∨ H.edge 2 a b := by
  classical
  by_cases hlex : LexEarlier H a b
  · exact Or.inl ((P.leaf_marker_one a b hab ha hb).mpr hlex)
  · exact Or.inr ((P.leaf_marker_two a b hab ha hb).mpr hlex)

/-- The missing capped-meet argument: two leaves a<b
already disagree as singleton types by the next cut a+1.
The disagreement is witnessed by one of the V3 markers
at ordered pair (1,a) or (2,a), while (1,a,a) and (2,a,a)
are nonedges because of the repeated terminal vertex. -/
theorem leaf_pair_disagrees_at_first_next_cut
    (P : RolePrediary H) (a b : Nat) (hab : a < b)
    (ha : IsLeaf H a) (hb : IsLeaf H b) :
    ¬ H.SameOneTypeBelow (a + 1) a b := by
  intro hs
  rcases P.leaf_pair_has_marker a b hab ha hb with hOne | hTwo
  · have hEq : H.edge 1 a a ↔ H.edge 1 a b :=
      hs (a := 1) (b := a) (by omega) (by omega)
    exact (P.repeated_vertex_nonedge 1 a) (hEq.mpr hOne)
  · have hEq : H.edge 2 a a ↔ H.edge 2 a b :=
      hs (a := 2) (b := a) (by omega) (by omega)
    exact (P.repeated_vertex_nonedge 2 a) (hEq.mpr hTwo)

end RolePrediary
end DiaryLeafPriority
end ThreeUniformDiaries
