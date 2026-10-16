import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Referee crosswalk: the Lean RoleDiary S2 cap equals the manuscript S2 cap

The exported RoleDiary.pair_meets field uses the shorthand
  fullMeet(P,Q) = min(first P, first Q)
for its capped alternative. The manuscript spells the cap as
  fullMeet(P,Q) = first P = first Q.

These are EQUIVALENT under S1: if two different first leaves
had full pair-meet equal to their lesser first coordinate,
the corresponding singleton leaf meet would also equal that
leaf, contradicting the required 1-split role.

This file proves the implication and the pairwise disjointness of
all three manuscript S2 cases. Thus the shorter existing Lean
field is not a weakening of S2 on a complete RoleDiary.
The proof is an important check for one-pass identity and
terminal-versus-normal pair-germ arguments.

It does not prove the proposed global one-pass completion.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Any full ordered-pair meet cannot exceed the meet of its
first singleton coordinates. -/
theorem twoMeetLevel_le_first_oneMeetLevel
    (H : Ordered3Graph Nat) (a b c d : Nat) :
    H.twoMeetLevel a b c d ≤ H.oneMeetLevel a c := by
  classical
  exact Nat.le_findGreatest
    (H.twoMeetLevel_le_min a b c d)
    (H.twoMeetLevel_agree a b c d).1

end Ordered3Graph

namespace DiaryLeafPriority
namespace RoleDiary

variable {H : Ordered3Graph Nat} (D : RoleDiary H)

/-- If the full pair meet is capped at the lesser minimum, S1
forces BOTH first components to be the same leaf. -/
theorem capped_pair_first_components_equal
    (D : RoleDiary H)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hcap : H.twoMeetLevel a b c d = min a c) :
    a = c := by
  by_contra hne
  have hsplit : IsOneSplit H (H.oneMeetLevel a c) :=
    D.singleton_meets a c ha hc hne
  have hle : min a c ≤ H.oneMeetLevel a c := by
    have hpair := H.twoMeetLevel_le_first_oneMeetLevel a b c d
    omega
  have heq : H.oneMeetLevel a c = min a c :=
    Nat.le_antisymm (H.oneMeetLevel_le_min a c) hle
  have hOne : IsOneSplit H (min a c) := by
    simpa only [heq] using hsplit
  have hLeaf : IsLeaf H (min a c) := by
    rcases le_total a c with hac | hca
    · simpa [min_eq_left hac] using ha
    · simpa [min_eq_right hca] using hc
  exact hLeaf.2.1 hOne.2.1

/-- This is the manuscript's EXACT S2 statement, recovered
without changing the library's existing compact API. -/
theorem pair_meets_exact_manuscript
    (D : RoleDiary H)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d) :
    H.twoMeetLevel a b c d = 1 ∨
      (H.twoMeetLevel a b c d = a ∧ a = c) ∨
      IsTwoSplit H (H.twoMeetLevel a b c d) := by
  rcases D.pair_meets a b c d hab hcd ha hb hc hd with
      hcap | hone | htwo
  · have hac := D.capped_pair_first_components_equal
      a b c d hab hcd ha hb hc hd hcap
    subst c
    exact Or.inr (Or.inl ⟨by simpa using hcap, rfl⟩)
  · exact Or.inl hone
  · exact Or.inr (Or.inr htwo)

/-- The three S2 alternatives are mutually exclusive, as
required by the manuscript's phrase 'precisely one'. -/
theorem pair_meets_cases_disjoint
    (D : RoleDiary H)
    (a b c d : Nat) (ha : IsLeaf H a) :
    ¬ (H.twoMeetLevel a b c d = 1 ∧
       (H.twoMeetLevel a b c d = a ∧ a = c)) ∧
    ¬ (H.twoMeetLevel a b c d = 1 ∧
       IsTwoSplit H (H.twoMeetLevel a b c d)) ∧
    ¬ ((H.twoMeetLevel a b c d = a ∧ a = c) ∧
       IsTwoSplit H (H.twoMeetLevel a b c d)) := by
  constructor
  · rintro ⟨hone, ⟨hcap, hac⟩⟩
    have ha3 := ha.1
    omega
  constructor
  · rintro ⟨hone, htwo⟩
    have hmin := htwo.1
    omega
  · rintro ⟨⟨hcap, hac⟩, htwo⟩
    have hOne : H.edge 0 2 a := by
      rw [← hcap]
      exact htwo.2.2
    exact ha.2.2 hOne

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
