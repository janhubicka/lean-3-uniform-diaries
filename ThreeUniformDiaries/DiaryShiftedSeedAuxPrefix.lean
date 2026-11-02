import ThreeUniformDiaries.DiaryShiftedSeedExactOneMeet

/-!
# Track B: auxiliary pair-prefix transport in the shifted diary seed

When a,b have the same original singleton type below m,
the auxiliary type of (m,a),(m,b) at every cut q <= m
is preserved under the three-marker shift. This is subtle:
new marker bits at vertices 1 and 2 are genuine auxiliary
tests for the shifted pairs. They agree because the true
source earlier-column Lex comparison of m with a/b agrees.

This lemma is valid for arbitrary enumerated 3-hypergraphs,
requires no diary axioms, and makes no assertion about
the still-unproved exact shifted full two-meet.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

theorem shiftedDiarySeed_sameAuxTypeBelow_of_source
    (H : Ordered3Graph Nat) (q m a b : Nat)
    (hma : m < a) (hmb : m < b) (hq : q ≤ m)
    (hAB : H.SameOneTypeBelow m a b)
    (hAux : H.SameAuxTypeBelow q m a m b) :
    (shiftedDiarySeed H).SameAuxTypeBelow (q+3)
      (m+3) (a+3) (m+3) (b+3) := by
  intro x hx
  have hxm : x < m+3 := by omega
  have hma' : m+3 < a+3 := by omega
  have hmb' : m+3 < b+3 := by omega
  have hLex : LexEarlier H m a ↔ LexEarlier H m b :=
    Ordered3Graph.lexEarlier_eq_of_common_one_prefix
      H m m a b hAB (by omega) hma hmb
  have hOld :
      (3 ≤ x ∧ H.edge (x-3) m a) ↔
      (3 ≤ x ∧ H.edge (x-3) m b) := by
    constructor
    · rintro ⟨hx3,he⟩
      exact ⟨hx3, (hAux (a := x-3) (by omega)).mp he⟩
    · rintro ⟨hx3,he⟩
      exact ⟨hx3, (hAux (a := x-3) (by omega)).mpr he⟩
  have hOne :
      (x = 1 ∧ 3 ≤ m+3 ∧ LexEarlier H m a) ↔
      (x = 1 ∧ 3 ≤ m+3 ∧ LexEarlier H m b) := by
    constructor
    · rintro ⟨hx,hy,he⟩
      exact ⟨hx,hy,hLex.mp he⟩
    · rintro ⟨hx,hy,he⟩
      exact ⟨hx,hy,hLex.mpr he⟩
  have hTwo :
      (x = 2 ∧ 3 ≤ m+3 ∧ ¬ LexEarlier H m a) ↔
      (x = 2 ∧ 3 ≤ m+3 ∧ ¬ LexEarlier H m b) := by
    constructor
    · rintro ⟨hx,hy,he⟩
      exact ⟨hx,hy,(not_congr hLex).mp he⟩
    · rintro ⟨hx,hy,he⟩
      exact ⟨hx,hy,(not_congr hLex).mpr he⟩
  change
    (x < m+3 ∧ m+3 < a+3 ∧
      ((3 ≤ x ∧ H.edge (x-3) m a) ∨
       (x = 1 ∧ 3 ≤ m+3 ∧ LexEarlier H m a) ∨
       (x = 2 ∧ 3 ≤ m+3 ∧ ¬ LexEarlier H m a))) ↔
    (x < m+3 ∧ m+3 < b+3 ∧
      ((3 ≤ x ∧ H.edge (x-3) m b) ∨
       (x = 1 ∧ 3 ≤ m+3 ∧ LexEarlier H m b) ∨
       (x = 2 ∧ 3 ≤ m+3 ∧ ¬ LexEarlier H m b)))
  simp only [hxm,hma',hmb',true_and,hOld,hOne,hTwo]

end DiaryLeafPriority
end ThreeUniformDiaries
