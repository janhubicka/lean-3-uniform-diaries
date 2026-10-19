import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.DiaryFiniteProtectedMeetPicture
import ThreeUniformDiaries.DiaryExactS2Cap

/-!
# Exact manuscript S2 and protected pictures for BOUNDED finite diaries

The finite RoleDiaryBlock interface records S1 for ordered
distinct leaves and S2 with the short capped alternative
fullMeet(P,Q)=min(first P,first Q). The published manuscript uses
the sharper cap: the two first leaves are IDENTICAL.

The sharpening is already proved for global RoleDiary, but a finite
edge table on Nat can never satisfy that global predicate on its
unused tail. We therefore reprove the short S1-to-cap argument
directly for a bounded finite diary.

As a consequence, every finite set of nonmarker vertices inside a
finite diary is an explicitly protected FiniteProtectedMeetPicture,
as required by relative one-pass completion. No global diary,
countable completion or flip absorption is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {n : Nat}

/-- The capped singleton agreement meet is symmetric for every
ordered ternary graph, without any diary axioms. -/
theorem finiteBlock_oneMeet_comm
    (H : Ordered3Graph Nat) (u v : Nat) :
    H.oneMeetLevel u v = H.oneMeetLevel v u := by
  classical
  apply le_antisymm
  · have hBound : H.oneMeetLevel u v ≤ min v u := by
      simpa only [min_comm] using H.oneMeetLevel_le_min u v
    apply Nat.le_findGreatest hBound
    have hAgree := H.oneMeetLevel_agree u v
    intro a b hab hb
    exact (hAgree hab hb).symm
  · have hBound : H.oneMeetLevel v u ≤ min u v := by
      simpa only [min_comm] using H.oneMeetLevel_le_min v u
    apply Nat.le_findGreatest hBound
    have hAgree := H.oneMeetLevel_agree v u
    intro a b hab hb
    exact (hAgree hab hb).symm

/-- Finite S1 applies to all DISTINCT bounded leaves, regardless
of which input order was supplied to the comparison. -/
theorem finiteRoleDiary_s1_unordered
    (D : FiniteRoleDiaryBlock H n)
    (u v : Nat) (hu : u < n) (hv : v < n)
    (hLeafU : IsLeaf H u) (hLeafV : IsLeaf H v)
    (hne : u ≠ v) :
    IsOneSplit H (H.oneMeetLevel u v) := by
  by_cases huv : u < v
  · exact D.singleton_meets u v huv hv hLeafU hLeafV
  · have hvu : v < u := by omega
    have hSplit := D.singleton_meets v u hvu hu hLeafV hLeafU
    rw [finiteBlock_oneMeet_comm H u v]
    exact hSplit

/-- Under finite S1 the short capped S2 alternative implies
that the two first leaves are literally the same source leaf. -/
theorem finiteRoleDiary_capped_first_eq
    (D : FiniteRoleDiaryBlock H n)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (hb : b < n) (hd : d < n)
    (ha : IsLeaf H a) (hbLeaf : IsLeaf H b)
    (hc : IsLeaf H c) (hdLeaf : IsLeaf H d)
    (hCap : H.twoMeetLevel a b c d = min a c) :
    a = c := by
  by_contra hne
  have han : a < n := by omega
  have hcn : c < n := by omega
  have hSplit : IsOneSplit H (H.oneMeetLevel a c) :=
    finiteRoleDiary_s1_unordered D a c han hcn ha hc hne
  have hGe : min a c ≤ H.oneMeetLevel a c := by
    have hLe := H.twoMeetLevel_le_first_oneMeetLevel a b c d
    omega
  have hEq : H.oneMeetLevel a c = min a c :=
    Nat.le_antisymm (H.oneMeetLevel_le_min a c) hGe
  have hOne : IsOneSplit H (min a c) := by
    simpa only [hEq] using hSplit
  have hLeaf : IsLeaf H (min a c) := by
    rcases le_total a c with hac | hca
    · simpa [min_eq_left hac] using ha
    · simpa [min_eq_right hca] using hc
  exact hLeaf.2.1 hOne.2.1

/-- EXACT finite manuscript S2: every full pair meet is marker
one, a genuine two-split, or a cap at a COMMON first leaf.
This matches the already verified global RoleDiary result but
requires only the two bounded finite S-axioms. -/
theorem finiteRoleDiary_pair_meets_exact
    (D : FiniteRoleDiaryBlock H n)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (hb : b < n) (hd : d < n)
    (ha : IsLeaf H a) (hbLeaf : IsLeaf H b)
    (hc : IsLeaf H c) (hdLeaf : IsLeaf H d) :
    H.twoMeetLevel a b c d = 1 ∨
      IsTwoSplit H (H.twoMeetLevel a b c d) ∨
      (a = c ∧ H.twoMeetLevel a b c d = a) := by
  rcases D.pair_meets a b c d hab hcd hb hd ha hbLeaf hc hdLeaf with
      hCap | hOne | hTwo
  · have hac := finiteRoleDiary_capped_first_eq
      D a b c d hab hcd hb hd ha hbLeaf hc hdLeaf hCap
    subst c
    exact Or.inr (Or.inr ⟨rfl, by simpa using hCap⟩)
  · exact Or.inl hOne
  · exact Or.inr (Or.inl hTwo)

/-- Every finite NONMARKER subpicture inside a bounded finite
diary has the exact S1/S2 protection conditions needed by the
verified one-pass relative completion theorem. -/
theorem finiteRoleDiary_protected_picture
    (D : FiniteRoleDiaryBlock H n)
    (F : Finset Nat)
    (hF : ∀ u : Nat, u ∈ F → 3 ≤ u ∧ u < n) :
    FiniteProtectedMeetPicture H F := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    exact (hF u hu).1
  · intro u v hu hv hLeafU hLeafV hne
    exact finiteRoleDiary_s1_unordered D u v
      (hF u hu).2 (hF v hv).2 hLeafU hLeafV hne
  · intro a b c d ha hb hc hd hab hcd
      haLeaf hbLeaf hcLeaf hdLeaf
    exact finiteRoleDiary_pair_meets_exact D
      a b c d hab hcd
      (hF b hb).2 (hF d hd).2
      haLeaf hbLeaf hcLeaf hdLeaf

end DiaryLeafPriority
end ThreeUniformDiaries
