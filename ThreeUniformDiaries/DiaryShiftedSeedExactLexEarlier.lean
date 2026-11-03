import ThreeUniformDiaries.DiaryShiftedSeedExactTwoMeet

/-!
# Track B: unconditional shifted three-marker seed V3 identity

This is the exact missing compatibility statement for diary existence.
For every original ordered 3-hypergraph H and a<b, the real
LexEarlier relation computed in its three-marker seed equals the
original LexEarlier relation, without any diary hypotheses.

At a capped singleton meet both comparisons are true.
At a proper singleton meet r, the deciding full pair meet moves
by exactly +3, and is strictly below r, so the seed's literal
old-edge reflection applies at a genuinely increasing triple.
There is no use of the false prediary universal old-cut property.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- The three-marker seed satisfies its genuine V3 compatibility
unconditionally, for every original ordered 3-hypergraph. -/
theorem shiftedDiarySeed_lexEarlier_iff
    (H : Ordered3Graph Nat) (a b : Nat) (hab : a < b) :
    LexEarlier (shiftedDiarySeed H) (a+3) (b+3) ↔
      LexEarlier H a b := by
  classical
  let S := shiftedDiarySeed H
  let r := H.oneMeetLevel a b
  have hShiftOne : S.oneMeetLevel (a+3) (b+3) = r+3 :=
    shiftedDiarySeed_oneMeetLevel_exact H a b hab
  have hrle : r ≤ a := by
    have h := H.oneMeetLevel_le_min a b
    omega
  by_cases hCap : r = a
  · have hSrc : LexEarlier H a b :=
      Or.inl ⟨hab, hCap⟩
    have hSeed : LexEarlier S (a+3) (b+3) := by
      apply Or.inl
      constructor
      · omega
      · rw [hShiftOne, hCap]
    exact iff_of_true hSeed hSrc
  · have hra : r < a := by omega
    have hrb : r < b := by omega
    have hFull :
        S.twoMeetLevel (r+3) (a+3) (r+3) (b+3) =
          H.twoMeetLevel r a r b + 3 :=
      shiftedDiarySeed_twoMeetLevel_exact_of_properOneMeet
        H a b hab hra
    have hAuxLt : H.auxMeetLevel r a r b < r := by
      change H.auxMeetLevel (H.oneMeetLevel a b) a
        (H.oneMeetLevel a b) b < H.oneMeetLevel a b
      exact H.auxMeetLevel_lt_proper_firstOneMeet a b hab hra
    have hFullLeAux :
        H.twoMeetLevel r a r b ≤ H.auxMeetLevel r a r b := by
      rw [H.twoMeetLevel_eq_min r a r b hra hrb]
      exact min_le_left _ _
    have hFullLt : H.twoMeetLevel r a r b < r :=
      lt_of_le_of_lt hFullLeAux hAuxLt
    have hEdge :
        S.edge (H.twoMeetLevel r a r b + 3) (r+3) (b+3) ↔
          H.edge (H.twoMeetLevel r a r b) r b :=
      shiftedDiarySeed_leaf_edge_iff H
        (H.twoMeetLevel r a r b) r b hFullLt hrb
    have hSourceForm :
        LexEarlier H a b ↔
          H.edge (H.twoMeetLevel r a r b) r b := by
      change
        ((a < b ∧ r = a) ∨
          (r < min a b ∧
            H.edge (H.twoMeetLevel r a r b) r b)) ↔
          H.edge (H.twoMeetLevel r a r b) r b
      have hCut : r < min a b := by omega
      simp only [hab, hCap, hCut, true_and, false_and, false_or]
    have hSeedForm :
        LexEarlier S (a+3) (b+3) ↔
          S.edge (H.twoMeetLevel r a r b + 3) (r+3) (b+3) := by
      change
        ((a+3 < b+3 ∧ S.oneMeetLevel (a+3) (b+3) = a+3) ∨
          (S.oneMeetLevel (a+3) (b+3) < min (a+3) (b+3) ∧
            S.edge
              (S.twoMeetLevel
                (S.oneMeetLevel (a+3) (b+3)) (a+3)
                (S.oneMeetLevel (a+3) (b+3)) (b+3))
              (S.oneMeetLevel (a+3) (b+3)) (b+3))) ↔
          S.edge (H.twoMeetLevel r a r b + 3) (r+3) (b+3)
      rw [hShiftOne]
      have hNotCap : r+3 ≠ a+3 := by omega
      have hCut : r+3 < min (a+3) (b+3) := by omega
      have hOrder : a+3 < b+3 := by omega
      simp only [hOrder, hNotCap, hCut, true_and, false_and, false_or]
      rw [hFull]
    exact hSeedForm.trans (hEdge.trans hSourceForm.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
