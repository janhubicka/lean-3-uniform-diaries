import ThreeUniformDiaries.DiaryOrientationUniformSign

/-!
# An ordered leaf-pair orientation anchor exists in every full diary

The Boolean global sign lemma takes a reference ordered leaf pair.
A complete countable role-based diary itself supplies one, without
assuming any additional colouring, genericity, or expansion property.

If vertex 3 is a one-split or two-split, the corresponding V1/V2
witnesses provide two distinct leaves. If it is a leaf, vertex 4
either is a second leaf or has one of the two split roles, which
again provide leaf witnesses. A V1 witness must consist of distinct
leaves: otherwise its singleton meet would be the leaf itself,
not the earlier one-split.

This removes a harmless but unnecessary nonemptiness premise from
the final global orientation preserve/reverse interface.
It does NOT prove the still-missing relative orientation premise.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph

variable {H : Ordered3Graph Nat} (D : RoleDiary H)

/-- V1 supplies an actual increasing ordered pair of leaves
witnessing an existing one-split. -/
theorem ordered_leaf_pair_of_oneSplit (D : RoleDiary H)
    (i : Nat) (hi : IsOneSplit H i) :
    Nonempty (OrderedLeafPair H) := by
  classical
  obtain ⟨u, v, hu, hv, hiu, hiv, hmeet⟩ :=
    D.one_split_witness i hi
  have hDistinct : u ≠ v := by
    intro heq
    subst v
    have hself : H.oneMeetLevel u u = u := by
      have hcap := H.oneMeetLevel_le_min u u
      have hagree : H.SameOneTypeBelow u u u := by
        intro a b hab hb
        rfl
      have hbelow : u ≤ H.oneMeetLevel u u :=
        Nat.le_findGreatest (by simp) hagree
      omega
    omega
  by_cases huv : u < v
  · exact ⟨⟨u, v, huv, hu, hv⟩⟩
  · have hvu : v < u := by omega
    exact ⟨⟨v, u, hvu, hv, hu⟩⟩

/-- V2 supplies an actual increasing ordered leaf pair from
either of the two pairs witnessing a two-split. -/
theorem ordered_leaf_pair_of_twoSplit (D : RoleDiary H)
    (i : Nat) (hi : IsTwoSplit H i) :
    Nonempty (OrderedLeafPair H) := by
  obtain ⟨a, b, c, d, hab, hcd, ha, hb, hc, hd,
    hia, hic, hmeet⟩ := D.two_split_witness i hi
  exact ⟨⟨a, b, hab, ha, hb⟩⟩

/-- Every full countable role-based diary has at least two
distinct leaves. Its V1/V2 witness properties plus the roles
of vertices 3 and 4 force this without a separate axiom. -/
theorem exists_ordered_leaf_pair (D : RoleDiary H) :
    Nonempty (OrderedLeafPair H) := by
  rcases D.role_valid 3 (by omega) with hLeaf3 | hOne3 | hTwo3
  · rcases D.role_valid 4 (by omega) with hLeaf4 | hOne4 | hTwo4
    · exact ⟨⟨3, 4, by omega, hLeaf3, hLeaf4⟩⟩
    · exact D.ordered_leaf_pair_of_oneSplit 4 hOne4
    · exact D.ordered_leaf_pair_of_twoSplit 4 hTwo4
  · exact D.ordered_leaf_pair_of_oneSplit 3 hOne3
  · exact D.ordered_leaf_pair_of_twoSplit 3 hTwo3

/-- For full diaries, a global relative lexicographic comparison
theorem gives a global preserve-or-reverse dichotomy without any
extra reference-pair or nonemptiness assumption. The target map
is still arbitrary at this purely logical stage. -/
theorem global_lex_sign_of_diary_relative
    (D : RoleDiary H) {K : Ordered3Graph Nat}
    (φ : Nat → Nat)
    (hrelative :
      ∀ p q : OrderedLeafPair H,
        (LexEarlier H p.first p.second ↔
         LexEarlier H q.first q.second) ↔
        (LexEarlier K (φ p.first) (φ p.second) ↔
         LexEarlier K (φ q.first) (φ q.second))) :
    (∀ p : OrderedLeafPair H,
       LexEarlier H p.first p.second ↔
         LexEarlier K (φ p.first) (φ p.second)) ∨
    (∀ p : OrderedLeafPair H,
       LexEarlier H p.first p.second ↔
         ¬ LexEarlier K (φ p.first) (φ p.second)) := by
  obtain ⟨reference⟩ := D.exists_ordered_leaf_pair
  exact global_lex_sign_of_relative φ reference hrelative

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
