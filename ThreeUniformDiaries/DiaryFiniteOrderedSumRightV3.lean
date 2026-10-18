import ThreeUniformDiaries.DiaryFiniteEOneSplitLex
import ThreeUniformDiaries.DiaryFiniteOrderedSumRightExactMeets
import ThreeUniformDiaries.DiaryFiniteOrderedSumPermittedEdges

/-!
# Preservation of both internal right-block Devlin V3 markers

Right-block leaf columns acquire cross Devlin bits at left middle
coordinates, so mere inducedness does NOT by itself prove the
lexicographic comparison on two right leaves. However these new
bits are identical for every right leaf: exact numerical one-meets
are shifted without splitting, as proved in the right transport.

For a finite source satisfying local S1 at its leaf pairs, the
first meet of two ordered right leaves is a genuine one-split
s>=3. The finite E-only comparison lemma identifies the literal
LexEarlier with the (0,s,rightLeaf) edge in BOTH source and
target. That edge is inside the induced right block, so the
lexicographic orientations coincide. Consequently the copied
source marker edges satisfy BOTH right-right V3 equivalences.

This is finite-block V3 only. It does not assert ambient V1/V2
witnesses, cross-block S1/S2, or a full finite ordered-sum diary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Exact literal LexEarlier transport for any two ordered right
source leaves, assuming only bounded source S1 and E1--E5 on
both finite inputs. Cross orientation bits remain arbitrary. -/
theorem finiteTwoBlockCarrier_right_lexEarlier_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hEH : ∀ x y z : Nat, H.edge x y z →
      PermittedDiaryEdge H x y z)
    (hEK : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (hS1 : ∀ a b : Nat, a < b → b < m →
      IsLeaf K a → IsLeaf K b →
      IsOneSplit K (K.oneMeetLevel a b))
    (bits : Nat → Bool)
    (a b : Nat) (hab : a < b) (hbm : b < m)
    (ha : IsLeaf K a) (hb : IsLeaf K b) :
    (LexEarlier (finiteTwoBlockCarrier H K n m bits)
        (rightBlockImage n a) (rightBlockImage n b) ↔
      LexEarlier K a b) := by
  let G := finiteTwoBlockCarrier H K n m bits
  let s := K.oneMeetLevel a b
  have hs : IsOneSplit K s := hS1 a b hab hbm ha hb
  have hsNe : s ≠ a := by
    intro he
    have hSplitA : IsOneSplit K a := by
      simpa only [he] using hs
    exact (oneSplit_not_leaf hSplitA) ha
  have hBound : s ≤ a := by
    have hle := K.oneMeetLevel_le_min a b
    dsimp [s]
    omega
  have hsa : s < a := by omega
  have hsb : s < b := by omega
  have hsm : s < m := by omega
  have ham : a < m := by omega
  have hMon := rightBlockImage_strictMono n FH.length_ge_three
  have hsG : IsOneSplit G (rightBlockImage n s) :=
    (finiteTwoBlockCarrier_right_oneSplit_iff
      FH FK bits s hs.1 hsm).mpr hs
  have hMeetTarget :
      G.oneMeetLevel (rightBlockImage n a) (rightBlockImage n b) =
        rightBlockImage n s :=
    finiteTwoBlockCarrier_right_oneMeet_exact
      FH FK hEK bits s a b hs.1
      ha.1 ham ha hb.1 hbm hb hsa hsb rfl
  have hEG : ∀ x y z : Nat, G.edge x y z →
      PermittedDiaryEdge G x y z := by
    intro x y z he
    exact finiteTwoBlockCarrier_permitted_edge
      FH FK hEH hEK bits x y z he
  have hSourceLex : LexEarlier K a b ↔ K.edge 0 s b :=
    E_oneSplit_lexEarlier_iff_right hEK s a b hs hab hsa rfl
  have hTargetLex :
      LexEarlier G (rightBlockImage n a) (rightBlockImage n b) ↔
        G.edge 0 (rightBlockImage n s) (rightBlockImage n b) :=
    E_oneSplit_lexEarlier_iff_right
      hEG (rightBlockImage n s)
      (rightBlockImage n a) (rightBlockImage n b)
      hsG (hMon hab) (hMon hsa) hMeetTarget
  have hMarkerZero : rightBlockImage n 0 = 0 :=
    rightBlockImage_marker n 0 (by omega)
  have hEdgeCopy :
      G.edge 0 (rightBlockImage n s) (rightBlockImage n b) ↔
        K.edge 0 s b := by
    simpa only [hMarkerZero] using
      (finiteTwoBlockCarrier_right_edge_iff_all FH FK bits 0 s b)
  exact hTargetLex.trans (hEdgeCopy.trans hSourceLex.symm)

/-- Both literal V3 Devlin marker laws hold for every ordered
pair of actual right source leaves in the ordered sum, from
bounded source S1/V3 and the E-shaped finite frames. -/
theorem finiteTwoBlockCarrier_right_V3_both
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hEH : ∀ x y z : Nat, H.edge x y z →
      PermittedDiaryEdge H x y z)
    (hEK : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (hS1 : ∀ a b : Nat, a < b → b < m →
      IsLeaf K a → IsLeaf K b →
      IsOneSplit K (K.oneMeetLevel a b))
    (hV3one : ∀ a b : Nat, a < b → b < m →
      IsLeaf K a → IsLeaf K b →
      (K.edge 1 a b ↔ LexEarlier K a b))
    (hV3two : ∀ a b : Nat, a < b → b < m →
      IsLeaf K a → IsLeaf K b →
      (K.edge 2 a b ↔ ¬ LexEarlier K a b))
    (bits : Nat → Bool)
    (a b : Nat) (hab : a < b) (hbm : b < m)
    (ha : IsLeaf K a) (hb : IsLeaf K b) :
    ((finiteTwoBlockCarrier H K n m bits).edge
        1 (rightBlockImage n a) (rightBlockImage n b) ↔
      LexEarlier (finiteTwoBlockCarrier H K n m bits)
        (rightBlockImage n a) (rightBlockImage n b)) ∧
    ((finiteTwoBlockCarrier H K n m bits).edge
        2 (rightBlockImage n a) (rightBlockImage n b) ↔
      ¬ LexEarlier (finiteTwoBlockCarrier H K n m bits)
        (rightBlockImage n a) (rightBlockImage n b)) := by
  have hLex := finiteTwoBlockCarrier_right_lexEarlier_iff
    FH FK hEH hEK hS1 bits a b hab hbm ha hb
  have hMarkerOne : rightBlockImage n 1 = 1 :=
    rightBlockImage_marker n 1 (by omega)
  have hMarkerTwo : rightBlockImage n 2 = 2 :=
    rightBlockImage_marker n 2 (by omega)
  have hEdgeOne :
      (finiteTwoBlockCarrier H K n m bits).edge
        1 (rightBlockImage n a) (rightBlockImage n b) ↔
          K.edge 1 a b := by
    simpa only [hMarkerOne] using
      (finiteTwoBlockCarrier_right_edge_iff_all FH FK bits 1 a b)
  have hEdgeTwo :
      (finiteTwoBlockCarrier H K n m bits).edge
        2 (rightBlockImage n a) (rightBlockImage n b) ↔
          K.edge 2 a b := by
    simpa only [hMarkerTwo] using
      (finiteTwoBlockCarrier_right_edge_iff_all FH FK bits 2 a b)
  exact ⟨hEdgeOne.trans ((hV3one a b hab hbm ha hb).trans hLex.symm),
    hEdgeTwo.trans ((hV3two a b hab hbm ha hb).trans
      (not_congr hLex.symm))⟩

end DiaryLeafPriority
end ThreeUniformDiaries
