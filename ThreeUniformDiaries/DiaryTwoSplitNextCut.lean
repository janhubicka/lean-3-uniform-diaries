import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# What a diary two-split adds to a full pair type

The five permitted hyperedge shapes prevent a vertex of the
two-split role from appearing in the middle position of an
increasing edge. Consequently passing the cut at a two-split i
cannot change either singleton coordinate of a full pair type.
The ONLY new information at cut i+1 is the bit edge(i,a,b).

We prove the exact equivalence, then obtain next-cut agreement
between two pairs incident with the same two-split using V2.
This is a structural fact of the complete diary V/E/S axioms,
not an extra synchronisation hypothesis.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

variable {H : Ordered3Graph Nat} (D : RoleDiary H)

/-- A two-split is never the middle vertex of an edge. Every
allowed edge has middle vertex marker 1/2, a one-split, or a leaf. -/
theorem twoSplit_no_middle (D : RoleDiary H)
    (i x v : Nat) (hm : IsTwoSplit H i) :
    ¬ H.edge x i v := by
  have hnotLeaf : ¬ IsLeaf H i := by
    intro h
    exact h.2.2 hm.2.2
  have hnotOne : ¬ IsOneSplit H i := by
    intro h
    exact hm.2.1 h.2.1
  intro he
  rcases D.permitted_edge x i v he with h₁ | h₂ | h₃ | h₄ | h₅
  · have hi := hm.1
    rcases h₁.2.1 with h | h <;> omega
  · exact hnotOne h₂.2.1
  · exact hnotLeaf h₃.2.1
  · exact hnotLeaf h₄.2.1
  · exact hnotLeaf h₅.2.1

/-- Source full pair-type equality across a two-split i is
equivalent to equality below i and equality of its single
new auxiliary incidence bit at i. Neither singleton type
gains a new bit, by the permitted-edge shapes. -/
theorem sameTwoTypeBelow_succ_iff_of_twoSplit (D : RoleDiary H)
    (i a b c d : Nat) (hm : IsTwoSplit H i) :
    H.SameTwoTypeBelow (i+1) a b c d ↔
      H.SameTwoTypeBelow i a b c d ∧
      (H.edge i a b ↔ H.edge i c d) := by
  constructor
  · intro hnext
    have hAux : H.SameAuxTypeBelow (i+1) a b c d := hnext.2.2
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · intro x y hxy hy
        exact hnext.1 hxy (by omega)
      · intro x y hxy hy
        exact hnext.2.1 hxy (by omega)
      · intro x hx
        exact hAux (a := x) (by omega)
    · exact hAux (a := i) (by omega)
  · rintro ⟨hold, hbit⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      by_cases hyold : y < i
      · exact hold.1 hxy hyold
      · have hyeq : y = i := by omega
        subst y
        constructor
        · intro he
          exact False.elim ((D.twoSplit_no_middle i x a hm) he)
        · intro he
          exact False.elim ((D.twoSplit_no_middle i x c hm) he)
    · intro x y hxy hy
      by_cases hyold : y < i
      · exact hold.2.1 hxy hyold
      · have hyeq : y = i := by omega
        subst y
        constructor
        · intro he
          exact False.elim ((D.twoSplit_no_middle i x b hm) he)
        · intro he
          exact False.elim ((D.twoSplit_no_middle i x d hm) he)
    · intro x hx
      by_cases hxold : x < i
      · exact hold.2.2 hxold
      · have hxeq : x = i := by omega
        subst x
        exact hbit

/-- Two pairs of leaves incident with a common 2-split have
the SAME full pair type through the successor cut. The V2
coherence axiom gives agreement below i; the incidence
edges both being present give the new bit. -/
theorem twoSplit_incident_pairTypes_succ (D : RoleDiary H)
    (i a b c d : Nat) (hm : IsTwoSplit H i)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hea : H.edge i a b) (hec : H.edge i c d) :
    H.SameTwoTypeBelow (i+1) a b c d := by
  apply (D.sameTwoTypeBelow_succ_iff_of_twoSplit i a b c d hm).2
  constructor
  · exact D.two_split_coherent i a b c d hm hab hcd
      ha hb hc hd hea hec
  · exact ⟨fun _ => hec, fun _ => hea⟩

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
