import ThreeUniformDiaries.DiaryLexColumnPrefixEarlier
import ThreeUniformDiaries.DiaryShiftedSeedPrediary

/-!
# Track B: exact singleton-meet shift for the three-marker diary seed

For any original ordered hypergraph H and a<b, the first singleton
type disagreement of the corresponding old vertices of the three-
marker seed occurs EXACTLY three positions later:
  oneMeet_S(a+3,b+3) = oneMeet_H(a,b)+3.

The key issue is that the new Devlin marker bits at 1 and 2 are
extra singleton type tests; their agreement before the first old
singleton disagreement follows from the COMMON-PREFIX LexEarlier
column theorem of the preceding Track B module.

No source diary axioms are assumed. This result covers capped and
proper first meets, and is independent of countable unavoidability,
the false prediary old-cut assertion, and the Ramsey theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- The new marker tests cannot distinguish the shifted copies of
a,b BEFORE the source's true singleton first-disagreement cut.
All source and target edge tests here are on increasing triples. -/
theorem shiftedDiarySeed_sameOneTypeBelow_of_source
    (H : Ordered3Graph Nat) (m a b : Nat)
    (hab : a < b) (hm : m ≤ a)
    (hAB : H.SameOneTypeBelow m a b) :
    (shiftedDiarySeed H).SameOneTypeBelow (m+3) (a+3) (b+3) := by
  intro x y hxy hy
  have hya : y < a+3 := by omega
  have hyb : y < b+3 := by omega
  have hOld :
      (3 ≤ x ∧ H.edge (x-3) (y-3) a) ↔
      (3 ≤ x ∧ H.edge (x-3) (y-3) b) := by
    constructor
    · rintro ⟨hx,he⟩
      have hxy' : x-3 < y-3 := by omega
      have hy' : y-3 < m := by omega
      exact ⟨hx,(hAB hxy' hy').mp he⟩
    · rintro ⟨hx,he⟩
      have hxy' : x-3 < y-3 := by omega
      have hy' : y-3 < m := by omega
      exact ⟨hx,(hAB hxy' hy').mpr he⟩
  have hOne :
      (x = 1 ∧ 3 ≤ y ∧ LexEarlier H (y-3) a) ↔
      (x = 1 ∧ 3 ≤ y ∧ LexEarlier H (y-3) b) := by
    constructor
    · rintro ⟨hx,hy3,he⟩
      have hLex := Ordered3Graph.lexEarlier_eq_of_common_one_prefix
        H m (y-3) a b hAB (by omega) (by omega) (by omega)
      exact ⟨hx,hy3,hLex.mp he⟩
    · rintro ⟨hx,hy3,he⟩
      have hLex := Ordered3Graph.lexEarlier_eq_of_common_one_prefix
        H m (y-3) a b hAB (by omega) (by omega) (by omega)
      exact ⟨hx,hy3,hLex.mpr he⟩
  have hTwo :
      (x = 2 ∧ 3 ≤ y ∧ ¬ LexEarlier H (y-3) a) ↔
      (x = 2 ∧ 3 ≤ y ∧ ¬ LexEarlier H (y-3) b) := by
    constructor
    · rintro ⟨hx,hy3,he⟩
      have hLex := Ordered3Graph.lexEarlier_eq_of_common_one_prefix
        H m (y-3) a b hAB (by omega) (by omega) (by omega)
      exact ⟨hx,hy3,(not_congr hLex).mp he⟩
    · rintro ⟨hx,hy3,he⟩
      have hLex := Ordered3Graph.lexEarlier_eq_of_common_one_prefix
        H m (y-3) a b hAB (by omega) (by omega) (by omega)
      exact ⟨hx,hy3,(not_congr hLex).mpr he⟩
  change
    (x < y ∧ y < a+3 ∧
      ((3 ≤ x ∧ H.edge (x-3) (y-3) a) ∨
        (x = 1 ∧ 3 ≤ y ∧ LexEarlier H (y-3) a) ∨
        (x = 2 ∧ 3 ≤ y ∧ ¬ LexEarlier H (y-3) a))) ↔
    (x < y ∧ y < b+3 ∧
      ((3 ≤ x ∧ H.edge (x-3) (y-3) b) ∨
        (x = 1 ∧ 3 ≤ y ∧ LexEarlier H (y-3) b) ∨
        (x = 2 ∧ 3 ≤ y ∧ ¬ LexEarlier H (y-3) b)))
  simp only [hxy,hya,hyb,true_and,hOld,hOne,hTwo]

/-- Exact numerical first singleton meet under the three-marker
shift. The upper bound uses an actual old first-disagreement
witness, not the invalid general type-to-aux implication. -/
theorem shiftedDiarySeed_oneMeetLevel_exact
    (H : Ordered3Graph Nat) (a b : Nat) (hab : a < b) :
    (shiftedDiarySeed H).oneMeetLevel (a+3) (b+3) =
      H.oneMeetLevel a b + 3 := by
  classical
  let S := shiftedDiarySeed H
  let m := H.oneMeetLevel a b
  have hSrcCap : m ≤ a := by
    have hb := H.oneMeetLevel_le_min a b
    omega
  have hSrcAgree : H.SameOneTypeBelow m a b :=
    H.oneMeetLevel_agree a b
  have hTargetAgree :
      S.SameOneTypeBelow (m+3) (a+3) (b+3) :=
    shiftedDiarySeed_sameOneTypeBelow_of_source H m a b
      hab hSrcCap hSrcAgree
  have hLo : m+3 ≤ S.oneMeetLevel (a+3) (b+3) :=
    Nat.le_findGreatest (by omega) hTargetAgree
  have hHi : S.oneMeetLevel (a+3) (b+3) ≤ m+3 := by
    by_cases hCap : m = a
    · have hBound := S.oneMeetLevel_le_min (a+3) (b+3)
      omega
    · have hmStrict : m < a := by omega
      by_contra hn
      have hBeyond : m+4 ≤ S.oneMeetLevel (a+3) (b+3) := by
        omega
      have hTargetNext :
          S.SameOneTypeBelow (m+4) (a+3) (b+3) := by
        have hagree := S.oneMeetLevel_agree (a+3) (b+3)
        intro x y hxy hy
        exact hagree hxy (by omega)
      have hSrcNext : H.SameOneTypeBelow (m+1) a b := by
        intro x y hxy hy
        have hShift : x+3 < y+3 := by omega
        have hyShift : y+3 < m+4 := by omega
        have hNew := hTargetNext hShift hyShift
        have hEdgeA :=
          shiftedDiarySeed_leaf_edge_iff H x y a hxy (by omega)
        have hEdgeB :=
          shiftedDiarySeed_leaf_edge_iff H x y b hxy (by omega)
        exact hEdgeA.symm.trans (hNew.trans hEdgeB)
      have hSrcBeyond : m+1 ≤ H.oneMeetLevel a b :=
        Nat.le_findGreatest (by omega) hSrcNext
      omega
  exact Nat.le_antisymm hHi hLo

end DiaryLeafPriority
end ThreeUniformDiaries
