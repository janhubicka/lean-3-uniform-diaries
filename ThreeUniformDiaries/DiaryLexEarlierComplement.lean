import ThreeUniformDiaries.DiaryOrientationReplacement
import ThreeUniformDiaries.DiaryPreembeddingOneSplit
import ThreeUniformDiaries.DiaryPreembeddingTwoSplit

/-!
# Lexicographic precedence reverses under swapping distinct vertices

The cut-zero five-vertex orientation gadget compares (2,3) with
(4,3), where the latter is in reverse enumeration order. To
re-express such a comparison using increasing ordered pairs it
is important that the manuscript's LexEarlier predicate is
complemented by reversing two distinct vertices.

We prove this directly for ANY enumerated 3-hypergraph, with no
diary-specific role or marker assumptions. The capped singleton
meet case is purely numerical. In the proper split case,
m = oneMeetLevel(a,b) lies before both vertices. The full mixed
pair meet for (m,a),(m,b) is the auxiliary meet q; the original
singleton first-disagreement witness forces q < m, and
maximality of q forces the two edge bits (q,m,a),(q,m,b) to
differ. Those are exactly the two opposite LexEarlier tests.

This is the underlying finite type-tree/tournament calculation;
it does not prove the still-missing global orientation
synchronisation from the five-vertex gadget.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- For every pair of DISTINCT vertices, lexicographic
precedence is exactly reversed by exchanging the vertices.
No linearity/role axioms are imposed on the source hypergraph. -/
theorem lexEarlier_swap_complement
    (H : Ordered3Graph Nat) (a b : Nat) (hne : a ≠ b) :
    LexEarlier H a b ↔ ¬ LexEarlier H b a := by
  classical
  let m := H.oneMeetLevel a b
  have hmComm : H.oneMeetLevel b a = m := by
    dsimp [m]
    exact H.oneMeetLevel_comm b a
  have hmCap : m ≤ min a b := H.oneMeetLevel_le_min a b
  by_cases hcap : m = min a b
  · by_cases hab : a < b
    · have hmA : m = a := by
        simpa [min_eq_left hab.le] using hcap
      have hLeft : LexEarlier H a b := by
        exact Or.inl ⟨hab, hmA⟩
      have hRight : ¬ LexEarlier H b a := by
        intro h
        rcases h with hfirst | hsecond
        · exact (not_lt_of_ge hab.le) hfirst.1
        · have hlt : H.oneMeetLevel b a < min b a := hsecond.1
          rw [hmComm, min_comm] at hlt
          omega
      exact iff_of_true hLeft hRight
    · have hba : b < a := by omega
      have hmB : m = b := by
        simpa [min_eq_right hba.le] using hcap
      have hLeft : ¬ LexEarlier H a b := by
        intro h
        rcases h with hfirst | hsecond
        · omega
        · have hlt : m < min a b := hsecond.1
          omega
      have hRight : LexEarlier H b a := by
        exact Or.inl ⟨hba, by simpa only [hmComm] using hmB⟩
      constructor
      · intro h
        exact False.elim (hLeft h)
      · intro h
        exact False.elim (h hRight)
  · have hmLt : m < min a b := by omega
    have hma : m < a := lt_of_lt_of_le hmLt (min_le_left a b)
    have hmb : m < b := lt_of_lt_of_le hmLt (min_le_right a b)
    let q := H.auxMeetLevel m a m b
    have hqCap : q ≤ m := by
      dsimp [q]
      simpa only [min_self] using H.auxMeetLevel_le_min m a m b
    have hqLt : q < m := by
      by_contra hnot
      have hqEq : q = m := by omega
      obtain ⟨z, hz, hdiff⟩ :=
        oneMeetLevel_has_first_witness H a b m rfl hma hmb
      have hauxQ : H.SameAuxTypeBelow q m a m b :=
        H.auxMeetLevel_agree m a m b
      have hauxM : H.SameAuxTypeBelow m m a m b := by
        simpa only [hqEq] using hauxQ
      exact hdiff (hauxM (a := z) hz)
    have hbits :
        ¬ (H.edge q m a ↔ H.edge q m b) := by
      intro hEq
      have hNext : H.SameAuxTypeBelow (q+1) m a m b := by
        intro z hz
        by_cases hzq : z < q
        · exact (H.auxMeetLevel_agree m a m b) (a := z) hzq
        · have heq : z = q := by omega
          subst z
          exact hEq
      have hbound : q+1 ≤ min m m := by omega
      have hGreater : q+1 ≤ H.auxMeetLevel m a m b :=
        Nat.le_findGreatest hbound hNext
      dsimp [q] at hGreater
      omega
    have hMixed : H.twoMeetLevel m a m b = q :=
      H.twoMeetLevel_mixed_eq_aux m a b hma hmb rfl
    have hMixedReverse : H.twoMeetLevel m b m a = q := by
      rw [H.twoMeetLevel_comm m b m a]
      exact hMixed
    have hNotA : m ≠ a := by omega
    have hNotB : m ≠ b := by omega
    have hLexAB : LexEarlier H a b ↔ H.edge q m b := by
      change ((a < b ∧ m = a) ∨
        (m < min a b ∧ H.edge (H.twoMeetLevel m a m b) m b)) ↔
        H.edge q m b
      rw [hMixed]
      simp [hNotA, hmLt]
    have hLexBA : LexEarlier H b a ↔ H.edge q m a := by
      dsimp only [LexEarlier]
      rw [hmComm]
      change ((b < a ∧ m = b) ∨
        (m < min b a ∧ H.edge (H.twoMeetLevel m b m a) m a)) ↔
        H.edge q m a
      rw [hMixedReverse]
      simp [hNotB, hmLt, min_comm]
    calc
      LexEarlier H a b ↔ H.edge q m b := hLexAB
      _ ↔ ¬ H.edge q m a := by
        by_cases ha : H.edge q m a <;>
          by_cases hb : H.edge q m b <;> simp_all
      _ ↔ ¬ LexEarlier H b a := not_congr hLexBA.symm

end DiaryLeafPriority
end ThreeUniformDiaries
