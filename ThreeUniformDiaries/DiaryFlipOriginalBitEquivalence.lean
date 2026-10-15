import ThreeUniformDiaries.DiaryFlipPrefixReconstruction

/-!
# Match the verified flip controls literally to the manuscript

The paper defines the bit p^A_B(m) asymmetrically, by the
existence of an actual edge of A that is absent in its flip B.
The verified local reconstruction lemmas use source-positive
leaf or leaf-pair witnesses.

For a genuine RoleDiary, the five E-edge shapes guarantee that
all such witnesses at a 1-split are leaves and all such
witnesses at a 2-split are ordered pairs of leaves.
Consequently no extra assumption was smuggled into the
finite-control bits of flip-prefix reconstruction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {A B : Ordered3Graph Nat}

/-- At a true 1-split, an edge of the form (0,m,w) can
only have a leaf at w. This is the E2 edge-shape
classification applied at an actually marked split. -/
theorem oneSplit_edge_has_leaf_endpoint
    (DA : RoleDiary A)
    (m w : Nat) (hm : IsOneSplit A m)
    (h : A.edge 0 m w) :
    IsLeaf A w := by
  rcases DA.permitted_edge 0 m w h with
    hrole | hone | htwo | hdev | hnormal
  · rcases hrole.2.1 with hy | hy
    · have hbound := hm.1
      omega
    · have hbound := hm.1
      omega
  · exact hone.2.2
  · have hbound := htwo.1.1
    omega
  · rcases hdev.1 with hx | hx <;> omega
  · have hbound := hnormal.1.1
    omega

/-- A true 2-split can only initiate an E3-edge whose
two other vertices are ordered leaves. -/
theorem twoSplit_edge_has_ordered_leaf_pair
    (DA : RoleDiary A)
    (m u v : Nat) (hm : IsTwoSplit A m)
    (h : A.edge m u v) :
    m < u ∧ u < v ∧ IsLeaf A u ∧ IsLeaf A v := by
  have horder := DA.edge_ordered m u v h
  rcases DA.permitted_edge m u v h with
    hrole | hone | htwo | hdev | hnormal
  · have hbound := hm.1
    omega
  · have hbound := hm.1
    omega
  · exact ⟨horder.1, horder.2, htwo.2.1, htwo.2.2⟩
  · have hbound := hm.1
    rcases hdev.1 with hx | hx <;> omega
  · have hleaf := hnormal.1
    exact False.elim (hleaf.2.2 hm.2.2)

/-- The verified one-split control is literally the
paper's existential p-bit, without an artificial
leaf-witness restriction. -/
theorem OneSplitRemovedBit_iff_paper
    (DA : RoleDiary A) (m : Nat) (hm : IsOneSplit A m) :
    OneSplitRemovedBit A B m ↔
      ∃ w, m < w ∧ A.edge 0 m w ∧ ¬ B.edge 0 m w := by
  constructor
  · rintro ⟨w, _, hmw, he, hn⟩
    exact ⟨w, hmw, he, hn⟩
  · rintro ⟨w, hmw, he, hn⟩
    exact ⟨w, DA.oneSplit_edge_has_leaf_endpoint
      m w hm he, hmw, he, hn⟩

/-- Likewise the two-split control is the paper's
existential p-bit over genuine later vertices. -/
theorem TwoSplitRemovedBit_iff_paper
    (DA : RoleDiary A) (m : Nat) (hm : IsTwoSplit A m) :
    TwoSplitRemovedBit A B m ↔
      ∃ u v, m < u ∧ m < v ∧
        A.edge m u v ∧ ¬ B.edge m u v := by
  constructor
  · rintro ⟨u, v, huv, hu, hv, hmu, he, hn⟩
    exact ⟨u, v, hmu, lt_trans hmu huv, he, hn⟩
  · rintro ⟨u, v, hmu, _, he, hn⟩
    obtain ⟨_, huv, hu, hv⟩ :=
      DA.twoSplit_edge_has_ordered_leaf_pair m u v hm he
    exact ⟨u, v, huv, hu, hv, hmu, he, hn⟩

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
