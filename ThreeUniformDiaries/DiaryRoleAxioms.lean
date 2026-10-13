import ThreeUniformDiaries.DiaryLeafPriority

/-!
# Marker roles and the two diary meet axioms

This is the structural bridge from actual marker edges to the
leaf-pair priority theorem. Only diary axioms (S1), (S2) are
required here; the V/E requirements enter later when constructing
ATR-admissible pointed envelopes.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Literal leaf and split roles of the manuscript's role-based
diary: the role is encoded by the two designated marker edges. -/
def IsLeaf (H : Ordered3Graph Nat) (v : Nat) : Prop :=
  3 ≤ v ∧ ¬ H.edge 0 1 v ∧ ¬ H.edge 0 2 v

def IsOneSplit (H : Ordered3Graph Nat) (v : Nat) : Prop :=
  3 ≤ v ∧ H.edge 0 1 v ∧ ¬ H.edge 0 2 v

def IsTwoSplit (H : Ordered3Graph Nat) (v : Nat) : Prop :=
  3 ≤ v ∧ ¬ H.edge 0 1 v ∧ H.edge 0 2 v

/-- The exact (S1), (S2) meet axioms restricted to leaf vertices.
No auxiliary type preservation is built into this definition. -/
structure RoleDiaryMeets (H : Ordered3Graph Nat) : Prop where
  singleton : ∀ a c, IsLeaf H a → IsLeaf H c → a ≠ c →
    IsOneSplit H (H.oneMeetLevel a c)
  pair : ∀ a b c d, a < b → c < d →
    IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
    H.twoMeetLevel a b c d = min a c ∨
    H.twoMeetLevel a b c d = 1 ∨
    IsTwoSplit H (H.twoMeetLevel a b c d)

private theorem singleton_meet_self (H : Ordered3Graph Nat) (a : Nat) :
    H.oneMeetLevel a a = a := by
  classical
  have hUpper : H.oneMeetLevel a a ≤ a := by
    simpa using H.oneMeetLevel_le_min a a
  have hAgree : H.SameOneTypeBelow a a a := by
    intro x y hxy hya
    rfl
  have hLower : a ≤ H.oneMeetLevel a a := by
    apply Nat.le_findGreatest (by simp)
    exact hAgree
  omega

namespace RoleDiaryMeets

/-- Any coordinate 1-type meet of two leaves is after marker 1
and has a role incompatible with a 2-split, including diagonal
comparisons of a leaf with itself. -/
theorem coordinate_meet_is_later
    {H : Ordered3Graph Nat} (D : RoleDiaryMeets H)
    {a c : Nat} (ha : IsLeaf H a) (hc : IsLeaf H c) :
    1 < H.oneMeetLevel a c ∧
    ¬ IsTwoSplit H (H.oneMeetLevel a c) := by
  by_cases hac : a = c
  · subst c
    rw [singleton_meet_self H a]
    constructor
    · have hbound := ha.1
      omega
    · intro ht
      exact ha.2.2 ht.2.2
  · have hsplit : IsOneSplit H (H.oneMeetLevel a c) :=
      D.singleton a c ha hc hac
    constructor
    · have hbound := hsplit.1
      omega
    · intro ht
      exact ht.2.1 hsplit.2.1

/-- Full and auxiliary meets agree for every pair of diary leaf
pairs, now expressed solely through actual edge-derived type levels
and the manuscript's marker and meet axioms. -/
theorem leaf_aux_eq_full
    {H : Ordered3Graph Nat} (D : RoleDiaryMeets H)
    {a b c d : Nat} (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d) :
    H.auxMeetLevel a b c d = H.twoMeetLevel a b c d := by
  obtain ⟨hfirst, hfirstNotTwo⟩ := D.coordinate_meet_is_later ha hc
  obtain ⟨hsecond, hsecondNotTwo⟩ := D.coordinate_meet_is_later hb hd
  exact auxMeetLevel_eq_twoMeetLevel_of_diary_cases H a b c d hab hcd
    (IsTwoSplit H) (D.pair a b c d hab hcd ha hb hc hd)
    hfirst hsecond hfirstNotTwo hsecondNotTwo

end RoleDiaryMeets
end DiaryLeafPriority
end ThreeUniformDiaries
