import ThreeUniformDiaries.CoordinateTree

/-!
# Meet closure of the enumeration coordinate in the finite encoder

The E0 coordinate consists of every finite enumeration node below
the prescribed initial n levels together with the chain of target
initial segments at selected levels e(i), for n <= i < m.
Two selected nodes lie on one chain and their meet is the earlier
one; meeting an arbitrary initial node gives another initial node.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- The E0 finite-coordinate candidate set from Lemma Aemb. -/
def finiteEnumCandidate {N : Nat}
    (H : EnumNode N) (e : Nat → Nat) (n m : Nat)
    (x : CoordNode) : Prop :=
  (∃ (k : Nat) (B : EnumNode k),
    k < n ∧ x = CoordNode.enum k B) ∨
  (∃ i : Nat, n ≤ i ∧ i < m ∧
    x = CoordNode.enum (e i) (H.truncate (e i)))

private theorem enumMeet_prefix_left
    (n i j : Nat) (B : EnumNode i) (C : EnumNode j)
    (hi : i < n) :
    ∃ (k : Nat) (D : EnumNode k),
      k < n ∧
        CoordNode.meet (.enum i B) (.enum j C) = .enum k D := by
  let k := CoordNode.meetLevel (.enum i B) (.enum j C)
  refine ⟨k, B.truncate k, ?_, rfl⟩
  exact lt_of_le_of_lt (CoordNode.meetLevel_le_left _ _) hi

private theorem enumMeet_prefix_right
    (n i j : Nat) (B : EnumNode i) (C : EnumNode j)
    (hj : j < n) :
    ∃ (k : Nat) (D : EnumNode k),
      k < n ∧
        CoordNode.meet (.enum i B) (.enum j C) = .enum k D := by
  let k := CoordNode.meetLevel (.enum i B) (.enum j C)
  refine ⟨k, B.truncate k, ?_, rfl⟩
  exact lt_of_le_of_lt (CoordNode.meetLevel_le_right _ _) hj

private theorem meet_eq_left_of_le
    (x y : CoordNode) (hxy : x ≤ y) :
    CoordNode.meet x y = x := by
  have hc : ∃ c : CoordNode, c ≤ x ∧ c ≤ y :=
    ⟨x, le_refl x, hxy⟩
  exact le_antisymm (CoordNode.meet_le_left hc)
    (CoordNode.le_meet (le_refl x) hxy)

private theorem meet_eq_right_of_le
    (x y : CoordNode) (hyx : y ≤ x) :
    CoordNode.meet x y = y := by
  have hc : ∃ c : CoordNode, c ≤ x ∧ c ≤ y :=
    ⟨y, hyx, le_refl y⟩
  exact le_antisymm (CoordNode.meet_le_right hc)
    (CoordNode.le_meet hyx (le_refl y))

/-- Along one enumerated target H, its truncations form a chain
in the actual coordinate tree. -/
private theorem enum_trunc_chain
    {N : Nat} (H : EnumNode N) (a b : Nat) (hab : a ≤ b) :
    CoordNode.enum a (H.truncate a) ≤
      CoordNode.enum b (H.truncate b) := by
  refine ⟨hab, ?_⟩
  change (H.truncate b).truncate a = H.truncate a
  exact H.truncate_truncate hab

/-- The actual E0 set is closed under tree meets. This proof needs
only the increasing selected level map; no type-respecting
hypothesis is involved in the enumeration coordinate. -/
theorem finiteEnumCandidate_meet
    {N : Nat} (H : EnumNode N) (e : Nat → Nat)
    (he : StrictMono e) (n m : Nat)
    (x y : CoordNode)
    (hx : finiteEnumCandidate H e n m x)
    (hy : finiteEnumCandidate H e n m y) :
    finiteEnumCandidate H e n m (CoordNode.meet x y) := by
  rcases hx with ⟨i, B, hi, rfl⟩ | ⟨i, hi, him, rfl⟩
  · rcases hy with ⟨j, C, hj, rfl⟩ | ⟨j, hj, hjm, rfl⟩
    · exact Or.inl (enumMeet_prefix_left n i j B C hi)
    · exact Or.inl (enumMeet_prefix_left n i (e j) B
        (H.truncate (e j)) hi)
  · rcases hy with ⟨j, C, hj, rfl⟩ | ⟨j, hj, hjm, rfl⟩
    · exact Or.inl (enumMeet_prefix_right n (e i) j
        (H.truncate (e i)) C hj)
    · rcases le_total i j with hij | hji
      · right
        refine ⟨i, hi, him, ?_⟩
        exact meet_eq_left_of_le _ _
          (enum_trunc_chain H (e i) (e j) (he.monotone hij))
      · right
        refine ⟨j, hj, hjm, ?_⟩
        exact meet_eq_right_of_le _ _
          (enum_trunc_chain H (e j) (e i) (he.monotone hji))

end EnumNode
end ThreeUniformDiaries
