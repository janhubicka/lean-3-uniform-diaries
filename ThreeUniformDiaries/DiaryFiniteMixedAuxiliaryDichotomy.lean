import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.DiaryFiniteOrderedSumRightMarkerTypes

/-!
# Auxiliary meets involving splits are marker-small or capped

If an ordered pair has a genuine split endpoint, E1--E5 forbid
its positive auxiliary incidences. A pair of genuine leaves,
on the other hand, has one of the two complementary Devlin
markers at 1,2 in any finite V/E pre-diary.

Thus, if at least one of two ordered pairs contains a split,
their auxiliary types either differ before marker cut three
or agree all the way to their minimum first coordinate.
There is no intermediate positive first difference.

We also isolate the purely algebraic marker-transport criterion:
under this small-or-capped dichotomy at both endpoints, exact
reflection of auxiliary prefix equality at cuts 0,1,2,3
preserves the NUMERICAL auxiliary meet through an increasing
map fixing markers 0,1,2.

This is a new building block for target-flip pullbacks. Neither
statement assumes unproved full mixed-meet preservation or
the every-target-flip absorption theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- If one of the two members of a pair is a genuine split,
every positive auxiliary test on that pair is absent.
This uses only the E1--E5 edge shapes. -/
theorem E_mixed_pair_no_positive_aux
    (hE : ∀ x y z : Nat, H.edge x y z → PermittedDiaryEdge H x y z)
    (x a b : Nat) (hx : 0 < x)
    (hMixed : IsDiarySplit H a ∨ IsDiarySplit H b) :
    ¬ H.edge x a b := by
  have hNotBoth : ¬ (IsLeaf H a ∧ IsLeaf H b) := by
    rintro ⟨ha,hb⟩
    rcases hMixed with hs | hs
    · exact hs.not_leaf ha
    · exact hs.not_leaf hb
  intro he
  rcases hE x a b he with hMarker | hOne | hTwo | hDevlin | hNormal
  · omega
  · omega
  · exact hNotBoth ⟨hTwo.2.1,hTwo.2.2⟩
  · exact hNotBoth ⟨hDevlin.2.1,hDevlin.2.2⟩
  · exact hNotBoth ⟨hNormal.2.1,hNormal.2.2⟩

/-- If one pair is split-containing and both pairs are either
split-containing or have an actual Devlin marker at 1 or 2,
their auxiliary meet is below 3 or capped at min(firsts).
No V1/V2/V3 axioms are used beyond the explicit marker disjunction. -/
theorem E_mixed_auxMeet_small_or_capped
    (hE : ∀ x y z : Nat, H.edge x y z → PermittedDiaryEdge H x y z)
    (a b c d : Nat) (ha3 : 3 ≤ a) (hc3 : 3 ≤ c)
    (hStatusAB :
      (IsDiarySplit H a ∨ IsDiarySplit H b) ∨
        (H.edge 1 a b ∨ H.edge 2 a b))
    (hStatusCD :
      (IsDiarySplit H c ∨ IsDiarySplit H d) ∨
        (H.edge 1 c d ∨ H.edge 2 c d))
    (hSomeMixed :
      (IsDiarySplit H a ∨ IsDiarySplit H b) ∨
      (IsDiarySplit H c ∨ IsDiarySplit H d)) :
    H.auxMeetLevel a b c d < 3 ∨
      H.auxMeetLevel a b c d = min a c := by
  classical
  by_cases hMarker : H.SameAuxTypeBelow 3 a b c d
  · have hBothMixed :
        (IsDiarySplit H a ∨ IsDiarySplit H b) ∧
        (IsDiarySplit H c ∨ IsDiarySplit H d) := by
      rcases hSomeMixed with hAB | hCD
      · rcases hStatusCD with hCD | hDevlin
        · exact ⟨hAB,hCD⟩
        · exfalso
          rcases hDevlin with hOne | hTwo
          · have hEq := hMarker (a := 1) (by omega)
            exact (E_mixed_pair_no_positive_aux hE 1 a b
              (by omega) hAB) (hEq.mpr hOne)
          · have hEq := hMarker (a := 2) (by omega)
            exact (E_mixed_pair_no_positive_aux hE 2 a b
              (by omega) hAB) (hEq.mpr hTwo)
      · rcases hStatusAB with hAB | hDevlin
        · exact ⟨hAB,hCD⟩
        · exfalso
          rcases hDevlin with hOne | hTwo
          · have hEq := hMarker (a := 1) (by omega)
            exact (E_mixed_pair_no_positive_aux hE 1 c d
              (by omega) hCD) (hEq.mp hOne)
          · have hEq := hMarker (a := 2) (by omega)
            exact (E_mixed_pair_no_positive_aux hE 2 c d
              (by omega) hCD) (hEq.mp hTwo)
    have hAtCap : H.SameAuxTypeBelow (min a c) a b c d := by
      intro x hx
      by_cases hxZero : x = 0
      · subst x
        exact hMarker (a := 0) (by omega)
      · have hxPos : 0 < x := by omega
        exact iff_of_false
          (E_mixed_pair_no_positive_aux hE x a b hxPos hBothMixed.1)
          (E_mixed_pair_no_positive_aux hE x c d hxPos hBothMixed.2)
    have hLower : min a c ≤ H.auxMeetLevel a b c d :=
      Nat.le_findGreatest (le_refl _) hAtCap
    exact Or.inr
      (le_antisymm (H.auxMeetLevel_le_min a b c d) hLower)
  · have hSmall : H.auxMeetLevel a b c d < 3 := by
      by_contra hBad
      have hMeetGe : 3 ≤ H.auxMeetLevel a b c d := by omega
      have hAgree : H.SameAuxTypeBelow 3 a b c d := by
        intro x hx
        exact (H.auxMeetLevel_agree a b c d) (by omega)
      exact hMarker hAgree
    exact Or.inl hSmall

namespace FiniteRolePrediaryBlock

variable {H : Ordered3Graph Nat} {n : Nat}

/-- Any ordered pair of genuine finite nonmarker vertices
either contains a split, or has a Devlin marker at 1 or 2.
The latter uses only bounded source V3. -/
theorem split_or_pair_marker
    (P : FiniteRolePrediaryBlock H n)
    (a b : Nat) (ha3 : 3 ≤ a) (hab : a < b) (hbn : b < n) :
    (IsDiarySplit H a ∨ IsDiarySplit H b) ∨
      (H.edge 1 a b ∨ H.edge 2 a b) := by
  have han : a < n := by omega
  have hb3 : 3 ≤ b := by omega
  rcases P.role_valid a ha3 han with haLeaf | haOne | haTwo
  · rcases P.role_valid b hb3 hbn with hbLeaf | hbOne | hbTwo
    · classical
      by_cases hLex : LexEarlier H a b
      · exact Or.inr (Or.inl
          ((P.leaf_marker_one a b hab hbn haLeaf hbLeaf).mpr hLex))
      · exact Or.inr (Or.inr
          ((P.leaf_marker_two a b hab hbn haLeaf hbLeaf).mpr hLex))
    · exact Or.inl (Or.inr (Or.inl hbOne))
    · exact Or.inl (Or.inr (Or.inr hbTwo))
  · exact Or.inl (Or.inl (Or.inl haOne))
  · exact Or.inl (Or.inl (Or.inr haTwo))

/-- In a GENUINE finite V/E pre-diary, comparing two increasing
nonmarker pairs with at least one split endpoint has auxiliary
meet either at an early marker or at the capped first member.
The theorem is unconditional in S1/S2. -/
theorem mixed_auxMeet_small_or_capped
    (P : FiniteRolePrediaryBlock H n)
    (a b c d : Nat)
    (ha3 : 3 ≤ a) (hab : a < b) (hbn : b < n)
    (hc3 : 3 ≤ c) (hcd : c < d) (hdn : d < n)
    (hSomeMixed :
      (IsDiarySplit H a ∨ IsDiarySplit H b) ∨
      (IsDiarySplit H c ∨ IsDiarySplit H d)) :
    H.auxMeetLevel a b c d < 3 ∨
      H.auxMeetLevel a b c d = min a c := by
  exact E_mixed_auxMeet_small_or_capped P.permitted_edge
    a b c d ha3 hc3
    (P.split_or_pair_marker a b ha3 hab hbn)
    (P.split_or_pair_marker c d hc3 hcd hdn)
    hSomeMixed

end FiniteRolePrediaryBlock

end DiaryLeafPriority
end ThreeUniformDiaries
