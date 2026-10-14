import ThreeUniformDiaries.DiaryFullRoleDefinition
import ThreeUniformDiaries.DiaryCanonicalPointedEnvelope
import ThreeUniformDiaries.DiaryPointedShapeTransport
import ThreeUniformDiaries.DiaryTwoTailShape
import ThreeUniformDiaries.DiaryPointedMeetCut

/-!
# The pointed diary pair envelope from one full diary hypothesis

This assembles the previously verified generic envelope calculations
using only the manuscript's role-based V/E/S diary definition, an
ordinary type-respecting image and a pair of diary leaves.

No separate marker, split-shape or pointed-profile axioms are supplied
by the caller. Every target level omitted by the embedding remains
in the retained full prefix, so the carrier formulas are literal.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

/-- The singleton meet of two distinct leaves is strictly before
either leaf, since S1 makes it a 1-split and the marker roles are
disjoint. This excludes the capped self-meet case explicitly. -/
theorem leaf_meet_lt_first
    {H : Ordered3Graph Nat} (D : RoleDiary H)
    (a b : Nat)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hne : a ≠ b) :
    H.oneMeetLevel a b < a := by
  have hm : IsOneSplit H (H.oneMeetLevel a b) :=
    D.singleton_meets a b ha hb hne
  have hle : H.oneMeetLevel a b ≤ a :=
    (H.oneMeetLevel_le_min a b).trans (min_le_left _ _)
  have hneA : H.oneMeetLevel a b ≠ a := by
    intro he
    have hs : IsOneSplit H a := by simpa only [he] using hm
    exact ha.2.1 hs.2.1
  omega

/-- The displayed two- or three-tail formulas really are the least
ordinary singleton/full-pair-meet envelopes of any image leaf pair.
This theorem has no abstract marker-shape premises. -/
theorem pointed_leaf_pair_minimal_cases
    {H K : Ordered3Graph Nat}
    (D : RoleDiary H)
    (ψ : Ordered3Graph.Embedding H K) (hψ : ψ.TypeRespecting)
    (i a b : Nat) (hi : 3 ≤ i)
    (hia : i ≤ a) (hab : a < b)
    (ha : IsLeaf H a) (hb : IsLeaf H b) :
    (H.oneMeetLevel a b < i ∧
      K.IsMinimalMeetEnvelope (ψ i) (ψ a) (ψ b)
        {x : Nat | x < ψ i ∨ x = ψ a ∨ x = ψ b}) ∨
    (i ≤ H.oneMeetLevel a b ∧
      K.IsMinimalMeetEnvelope (ψ i) (ψ a) (ψ b)
        {x : Nat | x < ψ i ∨
          x = ψ (H.oneMeetLevel a b) ∨ x = ψ a ∨ x = ψ b}) := by
  let m := H.oneMeetLevel a b
  by_cases hcase : m < i
  · exact Or.inl ⟨hcase,
      Ordered3Graph.two_tail_minimalMeetEnvelope_literal ψ hψ i a b hia hab hcase⟩
  · have him : i ≤ m := Nat.le_of_not_gt hcase
    have hm : IsOneSplit H m :=
      D.singleton_meets a b ha hb (ne_of_lt hab)
    have hma : m < a := D.leaf_meet_lt_first a b ha hb (ne_of_lt hab)
    exact Or.inr ⟨him,
      Ordered3Graph.role_three_tail_minimalMeetEnvelope_literal
        D.splitEdgeShape ψ hψ i m a b
        hi him hm ha hb hab hma rfl⟩

/-- Same full 2-type leaf pairs with meets after the cut yield
identical induced enumerated three-tail pictures, including all
triples meeting the protected prefix. This uses the corrected
Devlin-marker orientation obtained from the full diary definition. -/
theorem pointed_three_tail_shapes_of_same_leaf_two_type
    {H K : Ordered3Graph Nat}
    (D : RoleDiary H)
    (ψ : Ordered3Graph.Embedding H K) (hψ : ψ.TypeRespecting)
    (i a b c d : Nat) (hi : 3 ≤ i)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hpair : H.SameTwoTypeBelow i a b c d)
    (hcase : i ≤ H.oneMeetLevel a b)
    (x y z : Nat) (hxy : x < y) (hyz : y < z)
    (hz : z < ψ i + 3) :
    (K.pullback (threeTailInsertion
      (ψ i) (ψ (H.oneMeetLevel a b)) (ψ a) (ψ b))).edge x y z ↔
    (K.pullback (threeTailInsertion
      (ψ i) (ψ (H.oneMeetLevel c d)) (ψ c) (ψ d))).edge x y z := by
  let m := H.oneMeetLevel a b
  let n := H.oneMeetLevel c d
  have hbI : i ≤ b := hia.trans hab.le
  have hdI : i ≤ d := hic.trans hcd.le
  have hcases := H.sameTwoTypeBelow_same_envelope_case
    i a b c d hia hbI hic hdI hpair
  have hin : i ≤ n := by
    by_contra hn
    have hnlt : n < i := Nat.lt_of_not_ge hn
    have hmlt : m < i := hcases.mpr hnlt
    omega
  have hm : IsOneSplit H m :=
    D.singleton_meets a b ha hb (ne_of_lt hab)
  have hn : IsOneSplit H n :=
    D.singleton_meets c d hc hd (ne_of_lt hcd)
  have hma : m < a := D.leaf_meet_lt_first a b ha hb (ne_of_lt hab)
  have hnc : n < c := D.leaf_meet_lt_first c d hc hd (ne_of_lt hcd)
  let f : Nat → Nat := threeTailInsertion (ψ i) (ψ m) (ψ a) (ψ b)
  let g : Nat → Nat := threeTailInsertion (ψ i) (ψ n) (ψ c) (ψ d)
  exact (D.pointedEnvelopeAxioms).pointed_three_tail_shapes_after_type_embedding
    ψ hψ i m n a b c d hi hcase hin
    hm hn ha hb hc hd hab hcd hma hnc rfl rfl hpair
    f g
    (by intro t ht
        exact threeTailInsertion_fix_prefix (ψ i) (ψ m) (ψ a) (ψ b) t ht)
    (by intro t ht
        exact threeTailInsertion_fix_prefix (ψ i) (ψ n) (ψ c) (ψ d) t ht)
    (threeTailInsertion_split (ψ i) (ψ m) (ψ a) (ψ b))
    (threeTailInsertion_first (ψ i) (ψ m) (ψ a) (ψ b))
    (threeTailInsertion_second (ψ i) (ψ m) (ψ a) (ψ b))
    (threeTailInsertion_split (ψ i) (ψ n) (ψ c) (ψ d))
    (threeTailInsertion_first (ψ i) (ψ n) (ψ c) (ψ d))
    (threeTailInsertion_second (ψ i) (ψ n) (ψ c) (ψ d))
    x y z hxy hyz hz

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
