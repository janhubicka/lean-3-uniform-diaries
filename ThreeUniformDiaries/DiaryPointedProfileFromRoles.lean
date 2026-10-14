import ThreeUniformDiaries.DiaryRoleAxioms

/-!
# Mixed 2-type profiles determined by the diary role/edge axioms

The diary's full 2-type of a pair of leaves determines its split
orientation. A 1-split has the same incoming singleton type as
every other 1-split, while its mixed pairs with either leaf have
only one possible nonzero auxiliary bit below the split, at
marker 0. That bit is determined by the leaf pair's marker 1/2.

This file proves those consequences explicitly. It does not
assume the false general assertion that every type-respecting
embedding of an arbitrary diary preserves all auxiliary meets.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Exactly the additional role-based diary E/V edge-shape facts
used when comparing two pointed leaf-pair envelopes. These are
separate from the already formalised meet axioms (S1)/(S2). -/
structure RolePointedEnvelopeAxioms (H : Ordered3Graph Nat) : Prop where
  incoming :
    ∀ m x y, IsOneSplit H m → x < y → y < m →
      (H.edge x y m ↔ (x = 0 ∧ y = 1))
  earlierOnlyZero :
    ∀ m a z, IsOneSplit H m → IsLeaf H a →
      z < m → z ≠ 0 → ¬ H.edge z m a
  branchLeft :
    ∀ m a b, IsOneSplit H m → IsLeaf H a → IsLeaf H b →
      a < b → H.oneMeetLevel a b = m →
      (H.edge 0 m a ↔ H.edge 1 a b)
  branchRight :
    ∀ m a b, IsOneSplit H m → IsLeaf H a → IsLeaf H b →
      a < b → H.oneMeetLevel a b = m →
      (H.edge 0 m b ↔ H.edge 2 a b)
  noTerminalTriple :
    ∀ m a b, IsOneSplit H m → IsLeaf H a → IsLeaf H b →
      a < b → m < a → ¬ H.edge m a b

namespace RolePointedEnvelopeAxioms

/-- If two leaf pairs have the same full 2-type over i, and their
singletons split at 1-split vertices m,n not earlier than i, then
the two split vertices have equal 1-types and both mixed pairs
(split,first leaf) and (split,second leaf) have equal full 2-types.
The triples formed by each split and its leaves agree as well. -/
theorem pointed_profiles_of_leaf_pair_type
    {H : Ordered3Graph Nat} (D : RolePointedEnvelopeAxioms H)
    (i m n a b c d : Nat)
    (hi : 3 ≤ i) (him : i ≤ m) (hin : i ≤ n)
    (hm : IsOneSplit H m) (hn : IsOneSplit H n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hab : a < b) (hcd : c < d)
    (hma : m < a) (hnc : n < c)
    (hmeetAB : H.oneMeetLevel a b = m)
    (hmeetCD : H.oneMeetLevel c d = n)
    (hpair : H.SameTwoTypeBelow i a b c d) :
    H.SameOneTypeBelow i m n ∧
    H.SameTwoTypeBelow i m a n c ∧
    H.SameTwoTypeBelow i m b n d ∧
    (H.edge m a b ↔ H.edge n c d) := by
  have hsplit : H.SameOneTypeBelow i m n := by
    intro x y hxy hyi
    have hym : y < m := lt_of_lt_of_le hyi him
    have hyn : y < n := lt_of_lt_of_le hyi hin
    exact (D.incoming m x y hm hxy hym).trans
      (D.incoming n x y hn hxy hyn).symm
  have hleafAux : H.SameAuxTypeBelow i a b c d := hpair.2.2
  have hauxLeft : H.SameAuxTypeBelow i m a n c := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      have hmark : H.edge 1 a b ↔ H.edge 1 c d :=
        hleafAux (a := 1) (by omega)
      exact (D.branchLeft m a b hm ha hb hab hmeetAB).trans
        (hmark.trans (D.branchLeft n c d hn hc hd hcd hmeetCD).symm)
    · have hzm : z < m := lt_of_lt_of_le hz him
      have hzn : z < n := lt_of_lt_of_le hz hin
      exact iff_of_false
        (D.earlierOnlyZero m a z hm ha hzm hz0)
        (D.earlierOnlyZero n c z hn hc hzn hz0)
  have hauxRight : H.SameAuxTypeBelow i m b n d := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      have hmark : H.edge 2 a b ↔ H.edge 2 c d :=
        hleafAux (a := 2) (by omega)
      exact (D.branchRight m a b hm ha hb hab hmeetAB).trans
        (hmark.trans (D.branchRight n c d hn hc hd hcd hmeetCD).symm)
    · have hzm : z < m := lt_of_lt_of_le hz him
      have hzn : z < n := lt_of_lt_of_le hz hin
      exact iff_of_false
        (D.earlierOnlyZero m b z hm hb hzm hz0)
        (D.earlierOnlyZero n d z hn hd hzn hz0)
  have htriple : H.edge m a b ↔ H.edge n c d :=
    iff_of_false
      (D.noTerminalTriple m a b hm ha hb hab hma)
      (D.noTerminalTriple n c d hn hc hd hcd hnc)
  exact ⟨hsplit,
    ⟨hsplit, hpair.1, hauxLeft⟩,
    ⟨hsplit, hpair.2.1, hauxRight⟩,
    htriple⟩

end RolePointedEnvelopeAxioms
end DiaryLeafPriority
end ThreeUniformDiaries
