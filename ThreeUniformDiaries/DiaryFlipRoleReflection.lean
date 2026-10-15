import ThreeUniformDiaries.DiaryFlipTwoSplitControl

/-!
# Roles and permitted edge forms are unchanged by a diary flip

The identity diary-pre-embedding definition only states that
roles are preserved. Because the source is a genuine diary and
all three roles are pairwise incompatible, their preservation
is automatically reflection as well. Thus any edge in a flip
has one of the FIVE edge shapes of the original diary.

This removes the need to assume a common edge-shape mask when
comparing two flips. The initial role-marker bits (0,1,v),
(0,2,v) are identical in both flips at every vertex.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {A B C : Ordered3Graph Nat}

/-- A diary flip preserves and reflects the leaf role, even
though the specification only requested forward preservation. -/
theorem flip_leaf_iff
    (DA : RoleDiary A) (hAB : DiaryPreembeddingSpec A B id)
    (v : Nat) :
    IsLeaf A v ↔ IsLeaf B v := by
  constructor
  · exact hAB.leaf_role v
  · intro hv
    rcases DA.role_valid v hv.1 with hl | ho | ht
    · exact hl
    · have hb := hAB.one_split_role v ho
      exact False.elim (hv.2.1 hb.2.1)
    · have hb := hAB.two_split_role v ht
      exact False.elim (hv.2.2 hb.2.2)

/-- The same role reflection for one-splits. -/
theorem flip_oneSplit_iff
    (DA : RoleDiary A) (hAB : DiaryPreembeddingSpec A B id)
    (v : Nat) :
    IsOneSplit A v ↔ IsOneSplit B v := by
  constructor
  · exact hAB.one_split_role v
  · intro hv
    rcases DA.role_valid v hv.1 with hl | ho | ht
    · have hb := hAB.leaf_role v hl
      exact False.elim (hb.2.1 hv.2.1)
    · exact ho
    · have hb := hAB.two_split_role v ht
      exact False.elim (hv.2.2 hb.2.2)

/-- The same role reflection for two-splits. -/
theorem flip_twoSplit_iff
    (DA : RoleDiary A) (hAB : DiaryPreembeddingSpec A B id)
    (v : Nat) :
    IsTwoSplit A v ↔ IsTwoSplit B v := by
  constructor
  · exact hAB.two_split_role v
  · intro hv
    rcases DA.role_valid v hv.1 with hl | ho | ht
    · have hb := hAB.leaf_role v hl
      exact False.elim (hb.2.2 hv.2.2)
    · have hb := hAB.one_split_role v ho
      exact False.elim (hb.2.2 hv.2.2)
    · exact ht

/-- An edge of a flip has exactly one of the five edge-shape
types of the source diary. In particular no new unsupported
mixed edge can appear in a flip. -/
theorem flip_permitted_edge_of_target
    (DA : RoleDiary A) (DB : RoleDiary B)
    (hAB : DiaryPreembeddingSpec A B id)
    (x y z : Nat)
    (hedge : B.edge x y z) :
    PermittedDiaryEdge A x y z := by
  rcases DB.permitted_edge x y z hedge with
    hrole | hone | htwo | hdev | hnormal
  · exact Or.inl hrole
  · rcases hone with ⟨hx, hy, hz⟩
    exact Or.inr (Or.inl
      ⟨hx, (DA.flip_oneSplit_iff hAB y).mpr hy,
        (DA.flip_leaf_iff hAB z).mpr hz⟩)
  · rcases htwo with ⟨hx, hy, hz⟩
    exact Or.inr (Or.inr (Or.inl
      ⟨(DA.flip_twoSplit_iff hAB x).mpr hx,
        (DA.flip_leaf_iff hAB y).mpr hy,
        (DA.flip_leaf_iff hAB z).mpr hz⟩))
  · rcases hdev with ⟨hx, hy, hz⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hx, (DA.flip_leaf_iff hAB y).mpr hy,
        (DA.flip_leaf_iff hAB z).mpr hz⟩)))
  · rcases hnormal with ⟨hx, hy, hz⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨(DA.flip_leaf_iff hAB x).mpr hx,
        (DA.flip_leaf_iff hAB y).mpr hy,
        (DA.flip_leaf_iff hAB z).mpr hz⟩)))

/-- Marker-role edges agree in any two flips of a common diary.
The input is only a source role, and the two pre-embedding
specifications provide its exact target marker bits. -/
theorem two_flips_role_marker_edges_agree
    (DA : RoleDiary A)
    (hAB : DiaryPreembeddingSpec A B id)
    (hAC : DiaryPreembeddingSpec A C id)
    (v : Nat) (hv : 3 ≤ v) :
    (B.edge 0 1 v ↔ C.edge 0 1 v) ∧
    (B.edge 0 2 v ↔ C.edge 0 2 v) := by
  rcases DA.role_valid v hv with hl | ho | ht
  · have hb : IsLeaf B v := hAB.leaf_role v hl
    have hc : IsLeaf C v := hAC.leaf_role v hl
    exact ⟨iff_of_false hb.2.1 hc.2.1,
      iff_of_false hb.2.2 hc.2.2⟩
  · have hb : IsOneSplit B v := hAB.one_split_role v ho
    have hc : IsOneSplit C v := hAC.one_split_role v ho
    exact ⟨iff_of_true hb.2.1 hc.2.1,
      iff_of_false hb.2.2 hc.2.2⟩
  · have hb : IsTwoSplit B v := hAB.two_split_role v ht
    have hc : IsTwoSplit C v := hAC.two_split_role v ht
    exact ⟨iff_of_false hb.2.1 hc.2.1,
      iff_of_true hb.2.2 hc.2.2⟩

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
