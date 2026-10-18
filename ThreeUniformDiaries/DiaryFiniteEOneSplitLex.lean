import ThreeUniformDiaries.DiaryFullRoleDefinition
import Mathlib

/-!
# Finite E-only Lex orientation at a genuine one-split

If two leaves first disagree at a genuine 1-split s,
then exactly one of (0,s,a) and (0,s,b) is an edge.
All (x,s,z) with x>0 are forbidden by E1--E5, hence the
full mixed pair meet of (s,a) and (s,b) is zero.
The literal manuscript LexEarlier(a,b) is consequently the
right split incidence (0,s,b). No V1/V2/V3/S1/S2 assumptions.

Suitable for bounded finite diary blocks, unlike a global
RoleDiary predicate on all natural numbers.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- E1--E5 forbid positive auxiliary tests with one-split middle. -/
theorem E_oneSplit_no_positive_aux
    (hE : ∀ x y z : Nat, H.edge x y z → PermittedDiaryEdge H x y z)
    (s x z : Nat) (hs : IsOneSplit H s) (hx : 0 < x) :
    ¬ H.edge x s z := by
  have hNotLeaf : ¬ IsLeaf H s := by
    intro hl
    exact hl.2.1 hs.2.1
  intro he
  rcases hE x s z he with hMarker | hOne | hTwo | hDevlin | hNormal
  · omega
  · omega
  · exact hNotLeaf hTwo.2.1
  · exact hNotLeaf hDevlin.2.1
  · exact hNotLeaf hNormal.2.1

/-- At a genuine strict one-split, two leaves have opposite
zero-marker bit (0,s,_). -/
theorem E_oneSplit_distinguishing_zero_bit
    (hE : ∀ x y z : Nat, H.edge x y z → PermittedDiaryEdge H x y z)
    (s a b : Nat) (hs : IsOneSplit H s)
    (hab : a < b) (hsa : s < a)
    (hMeet : H.oneMeetLevel a b = s) :
    ¬ (H.edge 0 s a ↔ H.edge 0 s b) := by
  classical
  have hAgree : H.SameOneTypeBelow s a b := by
    rw [← hMeet]
    exact H.oneMeetLevel_agree a b
  have hNotNext : ¬ H.SameOneTypeBelow (s + 1) a b := by
    intro hNext
    have hCap : s + 1 ≤ min a b := by omega
    have hTooLarge : s + 1 ≤ H.oneMeetLevel a b :=
      Nat.le_findGreatest hCap hNext
    omega
  intro hZero
  apply hNotNext
  intro x y hxy hy
  by_cases hys : y < s
  · exact hAgree hxy hys
  · have hys' : y = s := by omega
    subst y
    by_cases hxZero : x = 0
    · subst x
      exact hZero
    · have hxPos : 0 < x := by omega
      exact iff_of_false
        (E_oneSplit_no_positive_aux hE s x a hs hxPos)
        (E_oneSplit_no_positive_aux hE s x b hs hxPos)

/-- The mixed auxiliary meet of (s,a), (s,b) is zero. -/
theorem E_oneSplit_mixed_aux_meet_zero
    (hE : ∀ x y z : Nat, H.edge x y z → PermittedDiaryEdge H x y z)
    (s a b : Nat) (hs : IsOneSplit H s)
    (hab : a < b) (hsa : s < a)
    (hMeet : H.oneMeetLevel a b = s) :
    H.auxMeetLevel s a s b = 0 := by
  have hBits := E_oneSplit_distinguishing_zero_bit
    hE s a b hs hab hsa hMeet
  by_contra hNotZero
  have hPositive : 0 < H.auxMeetLevel s a s b := by omega
  have hSame := H.auxMeetLevel_agree s a s b
  exact hBits (hSame hPositive)

/-- The full mixed meet is also zero. -/
theorem E_oneSplit_mixed_full_meet_zero
    (hE : ∀ x y z : Nat, H.edge x y z → PermittedDiaryEdge H x y z)
    (s a b : Nat) (hs : IsOneSplit H s)
    (hab : a < b) (hsa : s < a)
    (hMeet : H.oneMeetLevel a b = s) :
    H.twoMeetLevel s a s b = 0 := by
  have hsb : s < b := lt_trans hsa hab
  have hAux := E_oneSplit_mixed_aux_meet_zero
    hE s a b hs hab hsa hMeet
  rw [H.twoMeetLevel_eq_min s a s b hsa hsb, hAux]
  simp

/-- Literal LexEarlier is the right zero-marker incidence at an
actual one-split. No global diary hypothesis. -/
theorem E_oneSplit_lexEarlier_iff_right
    (hE : ∀ x y z : Nat, H.edge x y z → PermittedDiaryEdge H x y z)
    (s a b : Nat) (hs : IsOneSplit H s)
    (hab : a < b) (hsa : s < a)
    (hMeet : H.oneMeetLevel a b = s) :
    LexEarlier H a b ↔ H.edge 0 s b := by
  have hTwo := E_oneSplit_mixed_full_meet_zero
    hE s a b hs hab hsa hMeet
  change (a < b ∧ H.oneMeetLevel a b = a) ∨
    (H.oneMeetLevel a b < min a b ∧
      H.edge
        (H.twoMeetLevel (H.oneMeetLevel a b) a
          (H.oneMeetLevel a b) b)
        (H.oneMeetLevel a b) b) ↔ H.edge 0 s b
  constructor
  · rintro (⟨_, hcap⟩ | ⟨_, he⟩)
    · rw [hMeet] at hcap
      omega
    · simpa only [hMeet, hTwo] using he
  · intro he
    exact Or.inr ⟨by omega, by simpa only [hMeet, hTwo] using he⟩

end DiaryLeafPriority
end ThreeUniformDiaries
