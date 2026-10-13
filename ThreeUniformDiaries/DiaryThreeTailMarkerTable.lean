import ThreeUniformDiaries.DiaryAuxTransferWitness

/-!
# All exterior pairs in a three-vertex pointed diary envelope

The three pairs of the extra vertices are (m,a), (m,b), and
(a,b). The three manuscript marker witnesses at vertices 0,1,2
suffice for *all* six ordered comparisons of distinct pairs.
This supplies the finite-bound hypothesis of the prefix
auxiliary-envelope transfer criterion.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Swapping the two pair types does not change their auxiliary meet. -/
theorem auxMeetLevel_comm (H : Ordered3Graph Nat)
    (a b c d : Nat) :
    H.auxMeetLevel a b c d = H.auxMeetLevel c d a b := by
  classical
  have hBoundAB := H.auxMeetLevel_le_min a b c d
  have hBoundCD := H.auxMeetLevel_le_min c d a b
  have hAgreeAB := H.auxMeetLevel_agree a b c d
  have hAgreeCD := H.auxMeetLevel_agree c d a b
  have hLeft : H.auxMeetLevel a b c d ≤
      H.auxMeetLevel c d a b := by
    have hbound : H.auxMeetLevel a b c d ≤ min c a := by
      simpa only [min_comm] using hBoundAB
    have htype : H.SameAuxTypeBelow (H.auxMeetLevel a b c d) c d a b := by
      intro z hz
      exact (hAgreeAB (a := z) hz).symm
    exact Nat.le_findGreatest
      (P := fun k => H.SameAuxTypeBelow k c d a b)
      hbound htype
  have hRight : H.auxMeetLevel c d a b ≤
      H.auxMeetLevel a b c d := by
    have hbound : H.auxMeetLevel c d a b ≤ min a c := by
      simpa only [min_comm] using hBoundCD
    have htype : H.SameAuxTypeBelow (H.auxMeetLevel c d a b) a b c d := by
      intro z hz
      exact (hAgreeCD (a := z) hz).symm
    exact Nat.le_findGreatest
      (P := fun k => H.SameAuxTypeBelow k a b c d)
      hbound htype
  exact Nat.le_antisymm hLeft hRight

private theorem classify_three_tail_pair
    (n a b : Nat) (ha : n ≤ a) (hab : a < b)
    (hb : b < n+3) :
    (a=n ∧ b=n+1) ∨
      (a=n ∧ b=n+2) ∨
      (a=n+1 ∧ b=n+2) := by
  omega

/-- Marker disagreements at 0,1,2 decide every comparison
of different pairs chosen from a three-vertex exterior envelope.
No extra disagreement vertices need to be retained. -/
theorem three_tail_distinct_aux_meet_lt_prefix
    (H : Ordered3Graph Nat) (f : Nat → Nat)
    (n : Nat) (hn : 3 ≤ n)
    (h01 : H.auxMeetLevel
      (f n) (f (n+1)) (f n) (f (n+2)) ≤ 2)
    (h02 : H.auxMeetLevel
      (f n) (f (n+1)) (f (n+1)) (f (n+2)) ≤ 2)
    (h12 : H.auxMeetLevel
      (f n) (f (n+2)) (f (n+1)) (f (n+2)) ≤ 2)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hb : b < n+3) (hd : d < n+3)
    (ha : n ≤ a) (hc : n ≤ c)
    (hne : (a,b) ≠ (c,d)) :
    H.auxMeetLevel (f a) (f b) (f c) (f d) < n := by
  have h10 : H.auxMeetLevel
      (f n) (f (n+2)) (f n) (f (n+1)) ≤ 2 := by
    rw [H.auxMeetLevel_comm (f n) (f (n+2)) (f n) (f (n+1))]
    exact h01
  have h20 : H.auxMeetLevel
      (f (n+1)) (f (n+2)) (f n) (f (n+1)) ≤ 2 := by
    rw [H.auxMeetLevel_comm (f (n+1)) (f (n+2)) (f n) (f (n+1))]
    exact h02
  have h21 : H.auxMeetLevel
      (f (n+1)) (f (n+2)) (f n) (f (n+2)) ≤ 2 := by
    rw [H.auxMeetLevel_comm (f (n+1)) (f (n+2)) (f n) (f (n+2))]
    exact h12
  rcases classify_three_tail_pair n a b ha hab hb with hAB | hAB | hAB
  · rcases hAB with ⟨haEq, hbEq⟩
    subst a
    subst b
    rcases classify_three_tail_pair n c d hc hcd hd with hCD | hCD | hCD
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      exact (hne rfl).elim
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
  · rcases hAB with ⟨haEq, hbEq⟩
    subst a
    subst b
    rcases classify_three_tail_pair n c d hc hcd hd with hCD | hCD | hCD
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      exact (hne rfl).elim
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
  · rcases hAB with ⟨haEq, hbEq⟩
    subst a
    subst b
    rcases classify_three_tail_pair n c d hc hcd hd with hCD | hCD | hCD
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      omega
    · rcases hCD with ⟨hcEq, hdEq⟩
      subst c
      subst d
      exact (hne rfl).elim

end Ordered3Graph
end ThreeUniformDiaries
