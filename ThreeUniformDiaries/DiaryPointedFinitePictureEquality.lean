import ThreeUniformDiaries.DiaryPointedTypeConverse
import ThreeUniformDiaries.DiaryFinitePointedEnumNode

/-!
# Exact native finite EnumNode equality of same-type diary pair envelopes

The comparison theorems for two- or three-tail pointed diary envelopes
were initially stated as equality of induced increasing triples
on their selected carriers. The genuine finite ATR theorem, however,
colours `EnumNode m` structures, where non-increasing/out-of-level
triples are zero by definition.

This module bridges those statements: equality on all increasing
triples of actual finite vertices implies literal equality of the
native finite EnumNodes. Both the two-tail and role-based three-tail
cases are proved, allowing arbitrarily many omitted ambient levels.

It is this **equality of native finite sources**, not similarity of
their infinite tails, that permits the two canonical inclusions to
be regarded as finite embeddings of a single ATR source.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Agreement of induced triples on a finite initial segment of
two enumerations implies literal equality of the corresponding
native finite `EnumNode` hypergraphs. -/
theorem initialSegment_eq_of_induced_edge_agreement
    (K : Ordered3Graph Nat) (f g : Nat → Nat) (m : Nat)
    (hedge : ∀ x y z, x < y → y < z → z < m →
      ((K.pullback f).edge x y z ↔ (K.pullback g).edge x y z)) :
    ((K.pullback f).initialSegment m) =
      ((K.pullback g).initialSegment m) := by
  classical
  apply EnumNode.ext_triples
  funext x y z
  by_cases hvalid : x < y ∧ y < z ∧ z < m
  · obtain ⟨hxy, hyz, hz⟩ := hvalid
    have hiff := hedge x y z hxy hyz hz
    change K.edge (f x) (f y) (f z) ↔
      K.edge (g x) (g y) (g z) at hiff
    change decide (x < y ∧ y < z ∧ z < m ∧
        K.edge (f x) (f y) (f z)) =
      decide (x < y ∧ y < z ∧ z < m ∧
        K.edge (g x) (g y) (g z))
    by_cases he : K.edge (f x) (f y) (f z)
    · have hg : K.edge (g x) (g y) (g z) := hiff.mp he
      simp [hxy, hyz, hz, he, hg]
    · have hg : ¬ K.edge (g x) (g y) (g z) := by
        intro h
        exact he (hiff.mpr h)
      simp [hxy, hyz, hz, he, hg]
  · have hf : ((K.pullback f).initialSegment m).triple x y z = false :=
      ((K.pullback f).initialSegment m).support x y z hvalid
    have hg : ((K.pullback g).initialSegment m).triple x y z = false :=
      ((K.pullback g).initialSegment m).support x y z hvalid
    exact hf.trans hg.symm

/-- Source full 2-type equality is enough for literal equality
of the two prefix-plus-two-tail finite ATR sources after an ordinary
type-respecting embedding across any target gaps. -/
theorem two_tail_finiteEnum_eq_of_sameTwoType
    {H K : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i a b c d : Nat)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d)
    (hpair : H.SameTwoTypeBelow i a b c d) :
    ((K.pullback (twoTailInsertion (ψ i) (ψ a) (ψ b))).initialSegment
        (ψ i+2)) =
      ((K.pullback (twoTailInsertion (ψ i) (ψ c) (ψ d))).initialSegment
        (ψ i+2)) := by
  have hshape :=
    (two_tail_picture_equal_iff_source_pair_type
      ψ hψ i a b c d hia hic hab hcd).mpr hpair
  exact K.initialSegment_eq_of_induced_edge_agreement
    (twoTailInsertion (ψ i) (ψ a) (ψ b))
    (twoTailInsertion (ψ i) (ψ c) (ψ d))
    (ψ i+2) hshape

end Ordered3Graph

namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

/-- For a complete role-based diary, the two selected three-tail
finite ATR source nodes of same-full-2-type leaf pairs are
literally equal. The corrected Devlin marker correspondence,
including the protected prefix, is part of the proof. -/
theorem three_tail_finiteEnum_eq_of_same_leaf_twoType
    {H K : Ordered3Graph Nat}
    (D : RoleDiary H)
    (ψ : Ordered3Graph.Embedding H K)
    (hψ : ψ.TypeRespecting)
    (i a b c d : Nat) (hi : 3 ≤ i)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hpair : H.SameTwoTypeBelow i a b c d)
    (hcase : i ≤ H.oneMeetLevel a b) :
    ((K.pullback (threeTailInsertion
       (ψ i) (ψ (H.oneMeetLevel a b)) (ψ a) (ψ b))).initialSegment
        (ψ i+3)) =
      ((K.pullback (threeTailInsertion
       (ψ i) (ψ (H.oneMeetLevel c d)) (ψ c) (ψ d))).initialSegment
        (ψ i+3)) := by
  apply K.initialSegment_eq_of_induced_edge_agreement
  intro x y z hxy hyz hz
  exact D.pointed_three_tail_shapes_of_same_leaf_two_type
    ψ hψ i a b c d hi hia hic hab hcd
    ha hb hc hd hpair hcase x y z hxy hyz hz

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
