import ThreeUniformDiaries.DiaryFlipRoleReflection
import ThreeUniformDiaries.DiaryFourTailGenericRealization

/-!
# The flip-prefix reconstruction lemma for genuine V/E/S diaries

Let B,C be flips of the same role-based diary A, meaning that
the identity maps A→B and A→C are diary pre-embeddings.
Suppose the asymmetric source-positive removed-edge controls
at all 1- and 2-splits before a cut ell agree.

Then every triple whose middle vertex is before ell agrees
between B and C. We also recover the stronger condition for a
2-split as its first vertex before ell. In particular the
entire induced (ell+1)-vertex initial segments are identical.

The proof analyses only the five ACTUAL E-edge shapes:
role markers are fixed by their roles, E2/E3 by the two
verified local flip-bit reconstruction lemmas, Devlin edges
by the right 1-split bit at the leaf pair meet, and leaf
edges by the pre-embedding axiom.

No mixed-pair meet is postulated to be preserved. The result
is stated on Nat, as are the current RoleDiary and
DiaryPreembeddingSpec libraries; finite diary support is
a separate interface for the flip-tree absorption theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {A B C : Ordered3Graph Nat}

/-- Cancel the same source comparison twice without unfolding
the entire diary/meet development inside a propositional tactic. -/
private theorem anchor_comparison_cancel
    {P Q R X Y Z : Prop}
    (hPQ : (P ↔ Q) ↔ (X ↔ Y))
    (hPR : (P ↔ R) ↔ (X ↔ Z))
    (hYZ : Y ↔ Z) :
    Q ↔ R := by
  tauto

/-- At a leaf pair whose singleton meet lies before the cut,
agreement of its true 1-split flip bit forces BOTH Devlin
marker edge values (1,a,b) and (2,a,b) to agree. -/
theorem two_flips_devlin_markers_agree_of_oneSplit_bit
    (DA : RoleDiary A) (DB : RoleDiary B) (DC : RoleDiary C)
    (hAB : DiaryPreembeddingSpec A B id)
    (hAC : DiaryPreembeddingSpec A C id)
    (a b : Nat) (hab : a < b)
    (ha : IsLeaf A a) (hb : IsLeaf A b)
    (hbit :
      OneSplitRemovedBit A B (A.oneMeetLevel a b) ↔
      OneSplitRemovedBit A C (A.oneMeetLevel a b)) :
    (B.edge 1 a b ↔ C.edge 1 a b) ∧
    (B.edge 2 a b ↔ C.edge 2 a b) := by
  let m := A.oneMeetLevel a b
  have hm : IsOneSplit A m :=
    DA.singleton_meets a b ha hb (ne_of_lt hab)
  have hma : m < a :=
    DA.leaf_meet_lt_first a b ha hb (ne_of_lt hab)
  have hmb : m < b := lt_trans hma hab
  have hRight : B.edge 0 m b ↔ C.edge 0 m b :=
    DA.oneSplit_edges_agree_of_same_removed_bit
      DB DC hAB hAC m hm hbit b hb hmb
  have hMarker1B :=
    DA.flip_marker_one_agrees_iff_split_bit_agrees
      DB hAB a b hab ha hb
  have hMarker1C :=
    DA.flip_marker_one_agrees_iff_split_bit_agrees
      DC hAC a b hab ha hb
  have hMarker2B :=
    DA.flip_marker_two_agrees_iff_split_bit_agrees
      DB hAB a b hab ha hb
  have hMarker2C :=
    DA.flip_marker_two_agrees_iff_split_bit_agrees
      DC hAC a b hab ha hb
  constructor
  · change (A.edge 1 a b ↔ B.edge 1 a b) ↔
        (A.edge 0 m b ↔ B.edge 0 m b) at hMarker1B
    change (A.edge 1 a b ↔ C.edge 1 a b) ↔
        (A.edge 0 m b ↔ C.edge 0 m b) at hMarker1C
    exact anchor_comparison_cancel hMarker1B hMarker1C hRight
  · change (A.edge 2 a b ↔ B.edge 2 a b) ↔
        (A.edge 0 m b ↔ B.edge 0 m b) at hMarker2B
    change (A.edge 2 a b ↔ C.edge 2 a b) ↔
        (A.edge 0 m b ↔ C.edge 0 m b) at hMarker2C
    exact anchor_comparison_cancel hMarker2B hMarker2C hRight

/-- This is the corrected content of the manuscript's
flip prefix-reconstruction lemma: all triples with second
vertex below ell agree, as do all triples whose first
vertex is a 2-split below ell. -/
theorem two_flips_edge_iff_of_control_prefix
    (DA : RoleDiary A) (DB : RoleDiary B) (DC : RoleDiary C)
    (hAB : DiaryPreembeddingSpec A B id)
    (hAC : DiaryPreembeddingSpec A C id)
    (ell : Nat)
    (hOne : ∀ m, m < ell → IsOneSplit A m →
      (OneSplitRemovedBit A B m ↔ OneSplitRemovedBit A C m))
    (hTwo : ∀ m, m < ell → IsTwoSplit A m →
      (TwoSplitRemovedBit A B m ↔ TwoSplitRemovedBit A C m))
    (x y z : Nat) (hxy : x < y) (hyz : y < z)
    (hCut : y < ell ∨ (x < ell ∧ IsTwoSplit A x)) :
    B.edge x y z ↔ C.edge x y z := by
  classical
  by_cases hAny : B.edge x y z ∨ C.edge x y z
  · have hShape : PermittedDiaryEdge A x y z := by
      rcases hAny with hB | hC
      · exact DA.flip_permitted_edge_of_target
          DB hAB x y z hB
      · exact DA.flip_permitted_edge_of_target
          DC hAC x y z hC
    rcases hShape with hRole | hSplitOne | hSplitTwo | hDevlin | hNormal
    · rcases hRole with ⟨hx, hy, hz⟩
      subst x
      rcases hy with h1 | h2
      · subst y
        exact (DA.two_flips_role_marker_edges_agree
          hAB hAC z hz).1
      · subst y
        exact (DA.two_flips_role_marker_edges_agree
          hAB hAC z hz).2
    · rcases hSplitOne with ⟨hx, hy, hz⟩
      subst x
      have hyBefore : y < ell := by
        rcases hCut with hyBefore | ⟨_, hxRole⟩
        · exact hyBefore
        · have hbound := hxRole.1
          omega
      exact DA.oneSplit_edges_agree_of_same_removed_bit
        DB DC hAB hAC y hy (hOne y hyBefore hy)
        z hz hyz
    · rcases hSplitTwo with ⟨hx, hy, hz⟩
      have hxBefore : x < ell := by
        rcases hCut with hyBefore | ⟨hxBefore, _⟩
        · exact lt_trans hxy hyBefore
        · exact hxBefore
      exact DA.twoSplit_edges_agree_of_same_removed_bit
        DB DC hAB hAC x hx (hTwo x hxBefore hx)
        y z hyz hy hz hxy
    · rcases hDevlin with ⟨hx, hy, hz⟩
      have hyBefore : y < ell := by
        rcases hCut with hyBefore | ⟨_, hxRole⟩
        · exact hyBefore
        · rcases hx with h1 | h2
          · have hbound := hxRole.1
            omega
          · have hbound := hxRole.1
            omega
      have hm : IsOneSplit A (A.oneMeetLevel y z) :=
        DA.singleton_meets y z hy hz (ne_of_lt hyz)
      have hmy : A.oneMeetLevel y z < y :=
        DA.leaf_meet_lt_first y z hy hz (ne_of_lt hyz)
      have hbit :
          OneSplitRemovedBit A B (A.oneMeetLevel y z) ↔
          OneSplitRemovedBit A C (A.oneMeetLevel y z) :=
        hOne _ (lt_trans hmy hyBefore) hm
      have hMarkers :=
        two_flips_devlin_markers_agree_of_oneSplit_bit
          DA DB DC hAB hAC y z hyz hy hz hbit
      rcases hx with h1 | h2
      · subst x
        exact hMarkers.1
      · subst x
        exact hMarkers.2
    · rcases hNormal with ⟨hx, hy, hz⟩
      exact (hAB.leaf_edge_iff
        x y z hxy hyz hx hy hz).symm.trans
          (hAC.leaf_edge_iff x y z hxy hyz hx hy hz)
  · exact iff_of_false
      (fun h => hAny (Or.inl h))
      (fun h => hAny (Or.inr h))

/-- Consequently two such flips have LITERALLY identical
initial enumerated hypergraphs through ell, not merely
equal types at selected cuts. -/
theorem two_flips_initialSegment_eq_of_control_prefix
    (DA : RoleDiary A) (DB : RoleDiary B) (DC : RoleDiary C)
    (hAB : DiaryPreembeddingSpec A B id)
    (hAC : DiaryPreembeddingSpec A C id)
    (ell : Nat)
    (hOne : ∀ m, m < ell → IsOneSplit A m →
      (OneSplitRemovedBit A B m ↔ OneSplitRemovedBit A C m))
    (hTwo : ∀ m, m < ell → IsTwoSplit A m →
      (TwoSplitRemovedBit A B m ↔ TwoSplitRemovedBit A C m)) :
    B.initialSegment (ell+1) = C.initialSegment (ell+1) := by
  apply Ordered3Graph.initialSegment_eq_of_prefix_edge_agreement
    B C (ell+1)
  intro x y z hxy hyz hz
  have hyBefore : y < ell := by omega
  exact DA.two_flips_edge_iff_of_control_prefix
    DB DC hAB hAC ell hOne hTwo
    x y z hxy hyz (Or.inl hyBefore)

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
