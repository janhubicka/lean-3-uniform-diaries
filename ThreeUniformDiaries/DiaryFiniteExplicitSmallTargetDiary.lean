import ThreeUniformDiaries.DiaryFiniteExplicitSmallTarget
import ThreeUniformDiaries.DiaryFiniteFirstDisagreementCertificates
import ThreeUniformDiaries.DiaryFlipTwoSplitControl

/-!
# Complete bounded diary certificate for the explicit 9-vertex target

The ten-edge target has 3 as a two-split, 4 and 5 as
one-splits, and exactly three leaves 6,7,8. Its numerical
leaf meets and one nontrivial pair meet are established in
DiaryFiniteExplicitSmallTarget.

This follow-up checks the two remaining distinct-pair full
meet values at marker 1, the finite E1--E5 permitted edge
shapes and the exact role sets. The complete V/E/S block proof
will combine these concrete facts with the genuine split
witnesses, V3 orientations and S1/S2 enumerations.

This module is an actual mathematical example, not an
unverified finite decoder pretending to be a diary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

theorem smallFlipTarget_leaf_iff
    (z : Nat) (hz3 : 3 ≤ z) (hz9 : z < 9) :
    IsLeaf smallFlipTarget z ↔
      (z = 6 ∨ z = 7 ∨ z = 8) := by
  constructor
  · intro hz
    have hn3 : z ≠ 3 := by
      intro heq
      subst z
      exact hz.2.2 smallFlipTarget_twoSplit3.2.2
    have hn4 : z ≠ 4 := by
      intro heq
      subst z
      exact hz.2.1 smallFlipTarget_oneSplit4.2.1
    have hn5 : z ≠ 5 := by
      intro heq
      subst z
      exact hz.2.1 smallFlipTarget_oneSplit5.2.1
    omega
  · rintro (rfl | rfl | rfl)
    · exact smallFlipTarget_leaf6
    · exact smallFlipTarget_leaf7
    · exact smallFlipTarget_leaf8

theorem smallFlipTarget_permitted :
    ∀ x y z : Nat, smallFlipTarget.edge x y z →
      PermittedDiaryEdge smallFlipTarget x y z := by
  intro x y z he
  change
    (x = 0 ∧ y = 2 ∧ z = 3) ∨
    (x = 0 ∧ y = 1 ∧ z = 4) ∨
    (x = 0 ∧ y = 1 ∧ z = 5) ∨
    (x = 0 ∧ y = 4 ∧ z = 6) ∨
    (x = 0 ∧ y = 4 ∧ z = 8) ∨
    (x = 0 ∧ y = 5 ∧ z = 8) ∨
    (x = 2 ∧ y = 6 ∧ z = 7) ∨
    (x = 1 ∧ y = 6 ∧ z = 8) ∨
    (x = 1 ∧ y = 7 ∧ z = 8) ∨
    (x = 3 ∧ y = 6 ∧ z = 8) at he
  rcases he with
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact Or.inl ⟨rfl,Or.inr rfl,by omega⟩
  · exact Or.inl ⟨rfl,Or.inl rfl,by omega⟩
  · exact Or.inl ⟨rfl,Or.inl rfl,by omega⟩
  · exact Or.inr (Or.inl
      ⟨rfl,smallFlipTarget_oneSplit4,smallFlipTarget_leaf6⟩)
  · exact Or.inr (Or.inl
      ⟨rfl,smallFlipTarget_oneSplit4,smallFlipTarget_leaf8⟩)
  · exact Or.inr (Or.inl
      ⟨rfl,smallFlipTarget_oneSplit5,smallFlipTarget_leaf8⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Or.inr rfl,smallFlipTarget_leaf6,smallFlipTarget_leaf7⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Or.inl rfl,smallFlipTarget_leaf6,smallFlipTarget_leaf8⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Or.inl rfl,smallFlipTarget_leaf7,smallFlipTarget_leaf8⟩)))
  · exact Or.inr (Or.inr (Or.inl
      ⟨smallFlipTarget_twoSplit3,smallFlipTarget_leaf6,
        smallFlipTarget_leaf8⟩))

/-- The pair (6,7) and pair (6,8) disagree immediately at the
marker-1 auxiliary incidence, so their full type meet is 1. -/
theorem smallFlipTarget_twoType_67_68_at_one :
    smallFlipTarget.SameTwoTypeBelow 1 6 7 6 8 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    omega
  · intro x y hxy hy
    omega
  · intro x hx
    have hx0 : x = 0 := by omega
    subst x
    simp [smallFlipTarget]

theorem smallFlipTarget_twoMeet_67_68 :
    smallFlipTarget.twoMeetLevel 6 7 6 8 = 1 := by
  apply Ordered3Graph.twoMeetLevel_eq_of_aux_first_disagreement
    smallFlipTarget 6 7 6 8 1 (by omega)
    smallFlipTarget_twoType_67_68_at_one
  simp [smallFlipTarget]

/-- The pair (6,7) and pair (7,8) likewise differ already
at marker-1 auxiliary incidence, so their full meet is 1. -/
theorem smallFlipTarget_twoType_67_78_at_one :
    smallFlipTarget.SameTwoTypeBelow 1 6 7 7 8 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    omega
  · intro x y hxy hy
    omega
  · intro x hx
    have hx0 : x = 0 := by omega
    subst x
    simp [smallFlipTarget]

theorem smallFlipTarget_twoMeet_67_78 :
    smallFlipTarget.twoMeetLevel 6 7 7 8 = 1 := by
  apply Ordered3Graph.twoMeetLevel_eq_of_aux_first_disagreement
    smallFlipTarget 6 7 7 8 1 (by omega)
    smallFlipTarget_twoType_67_78_at_one
  simp [smallFlipTarget]



/-- Lexicographic orientation of the three actual ordered
target leaf pairs follows from the one-split right-branch
formula, not from a separately postulated marker order. -/
theorem smallFlipTarget_lex67_false :
    ¬ LexEarlier smallFlipTarget 6 7 := by
  intro h
  have hLex := E_oneSplit_lexEarlier_iff_right
    smallFlipTarget_permitted
    4 6 7 smallFlipTarget_oneSplit4
    (by omega) (by omega) smallFlipTarget_meet_6_7
  have hEdge := hLex.mp h
  simp [smallFlipTarget] at hEdge

theorem smallFlipTarget_lex68_true :
    LexEarlier smallFlipTarget 6 8 := by
  have hLex := E_oneSplit_lexEarlier_iff_right
    smallFlipTarget_permitted
    5 6 8 smallFlipTarget_oneSplit5
    (by omega) (by omega) smallFlipTarget_meet_6_8
  apply hLex.mpr
  simp [smallFlipTarget]

theorem smallFlipTarget_lex78_true :
    LexEarlier smallFlipTarget 7 8 := by
  have hLex := E_oneSplit_lexEarlier_iff_right
    smallFlipTarget_permitted
    4 7 8 smallFlipTarget_oneSplit4
    (by omega) (by omega) smallFlipTarget_meet_7_8
  apply hLex.mpr
  simp [smallFlipTarget]

/-- Every increasing pair of target leaves is one of
(6,7), (6,8), (7,8). This avoids any implicit claim about
the artificial infinite zero-edge tail. -/
theorem smallFlipTarget_ordered_leaf_pair_cases
    (a b : Nat) (hab : a < b) (hb9 : b < 9)
    (ha : IsLeaf smallFlipTarget a)
    (hb : IsLeaf smallFlipTarget b) :
    (a = 6 ∧ b = 7) ∨ (a = 6 ∧ b = 8) ∨
      (a = 7 ∧ b = 8) := by
  have haCases := (smallFlipTarget_leaf_iff
    a ha.1 (by omega)).mp ha
  have hbCases := (smallFlipTarget_leaf_iff
    b hb.1 hb9).mp hb
  omega

/-- All bounded finite V/E/S axioms of the explicit nine-vertex
target, including genuine two-split witness and every capped S2
case. This is a full mathematical diary certificate, not just
a syntactic check on its edge table. -/
theorem smallFlipTarget_is_finiteDiary :
    FiniteRoleDiaryBlock smallFlipTarget 9 := by
  refine {
    prediary := {
      frame := smallFlipTarget_frame
      role_valid := ?_
      one_split_coherent := ?_
      one_split_witness := ?_
      two_split_coherent := ?_
      two_split_witness := ?_
      leaf_marker_one := ?_
      leaf_marker_two := ?_
      permitted_edge := smallFlipTarget_permitted
    }
    singleton_meets := ?_
    pair_meets := ?_
  }
  · intro z hz3 hz9
    have hz : z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨
        z = 7 ∨ z = 8 := by omega
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr smallFlipTarget_twoSplit3)
    · exact Or.inr (Or.inl smallFlipTarget_oneSplit4)
    · exact Or.inr (Or.inl smallFlipTarget_oneSplit5)
    · exact Or.inl smallFlipTarget_leaf6
    · exact Or.inl smallFlipTarget_leaf7
    · exact Or.inl smallFlipTarget_leaf8
  · intro s a b hs _ha _hb hsa hsb
    rcases smallFlipTarget_oneSplit_eq_four_or_five hs with rfl | rfl
    · have haCase : a = 6 ∨ a = 8 := by
        simp [smallFlipTarget] at hsa
        omega
      have hbCase : b = 6 ∨ b = 8 := by
        simp [smallFlipTarget] at hsb
        omega
      rcases haCase with rfl | rfl
      · rcases hbCase with rfl | rfl
        · intro x y _ _
          exact Iff.rfl
        · intro x y hxy hy
          exact smallFlipTarget_oneType_6_8_at_five hxy (by omega)
      · rcases hbCase with rfl | rfl
        · intro x y hxy hy
          exact (smallFlipTarget_oneType_6_8_at_five
            hxy (by omega)).symm
        · intro x y _ _
          exact Iff.rfl
    · have ha8 : a = 8 := by
        simp [smallFlipTarget] at hsa
        omega
      have hb8 : b = 8 := by
        simp [smallFlipTarget] at hsb
        omega
      subst a
      subst b
      intro x y _ _
      exact Iff.rfl
  · intro s hs _hsk
    rcases smallFlipTarget_oneSplit_eq_four_or_five hs with rfl | rfl
    · exact ⟨6,7,by omega,by omega,
        smallFlipTarget_leaf6,smallFlipTarget_leaf7,
        by omega,by omega,smallFlipTarget_meet_6_7⟩
    · exact ⟨6,8,by omega,by omega,
        smallFlipTarget_leaf6,smallFlipTarget_leaf8,
        by omega,by omega,smallFlipTarget_meet_6_8⟩
  · intro s a b c d hs _hab _hcd _ha _hb _hc _hd hposAB hposCD
    have hs3 : s = 3 := smallFlipTarget_twoSplit_eq_three hs
    subst s
    have hAB : a = 6 ∧ b = 8 := by
      simp [smallFlipTarget] at hposAB
      omega
    have hCD : c = 6 ∧ d = 8 := by
      simp [smallFlipTarget] at hposCD
      omega
    rcases hAB with ⟨rfl,rfl⟩
    rcases hCD with ⟨rfl,rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x y _ _
      exact Iff.rfl
    · intro x y _ _
      exact Iff.rfl
    · intro x _
      exact Iff.rfl
  · intro s hs _hsk
    have hs3 : s = 3 := smallFlipTarget_twoSplit_eq_three hs
    subst s
    exact ⟨6,8,7,8,by omega,by omega,
      by omega,by omega,by omega,by omega,
      smallFlipTarget_leaf6,smallFlipTarget_leaf8,
      smallFlipTarget_leaf7,smallFlipTarget_leaf8,
      by omega,by omega,smallFlipTarget_twoMeet_68_78⟩
  · intro a b hab hb ha hbLeaf
    rcases smallFlipTarget_ordered_leaf_pair_cases
      a b hab hb ha hbLeaf with
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · change smallFlipTarget.edge 1 6 7 ↔
        LexEarlier smallFlipTarget 6 7
      exact iff_of_false (by simp [smallFlipTarget])
        smallFlipTarget_lex67_false
    · change smallFlipTarget.edge 1 6 8 ↔
        LexEarlier smallFlipTarget 6 8
      exact iff_of_true (by simp [smallFlipTarget])
        smallFlipTarget_lex68_true
    · change smallFlipTarget.edge 1 7 8 ↔
        LexEarlier smallFlipTarget 7 8
      exact iff_of_true (by simp [smallFlipTarget])
        smallFlipTarget_lex78_true
  · intro a b hab hb ha hbLeaf
    rcases smallFlipTarget_ordered_leaf_pair_cases
      a b hab hb ha hbLeaf with
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · change smallFlipTarget.edge 2 6 7 ↔
        ¬ LexEarlier smallFlipTarget 6 7
      exact iff_of_true (by simp [smallFlipTarget])
        smallFlipTarget_lex67_false
    · change smallFlipTarget.edge 2 6 8 ↔
        ¬ LexEarlier smallFlipTarget 6 8
      exact iff_of_false (by simp [smallFlipTarget])
        (not_not_intro smallFlipTarget_lex68_true)
    · change smallFlipTarget.edge 2 7 8 ↔
        ¬ LexEarlier smallFlipTarget 7 8
      exact iff_of_false (by simp [smallFlipTarget])
        (not_not_intro smallFlipTarget_lex78_true)
  · intro a b hab hb ha hbLeaf
    rcases smallFlipTarget_ordered_leaf_pair_cases
      a b hab hb ha hbLeaf with
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [smallFlipTarget_meet_6_7]
      exact smallFlipTarget_oneSplit4
    · rw [smallFlipTarget_meet_6_8]
      exact smallFlipTarget_oneSplit5
    · rw [smallFlipTarget_meet_7_8]
      exact smallFlipTarget_oneSplit4
  · intro a b c d hab hcd hb hd ha hbLeaf hc hdLeaf
    have hAB := smallFlipTarget_ordered_leaf_pair_cases
      a b hab hb ha hbLeaf
    have hCD := smallFlipTarget_ordered_leaf_pair_cases
      c d hcd hd hc hdLeaf
    rcases hAB with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      rcases hCD with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · left
      simpa using Ordered3Graph.twoMeetLevel_self_eq
        smallFlipTarget 6 7 (by omega)
    · exact Or.inr (Or.inl smallFlipTarget_twoMeet_67_68)
    · exact Or.inr (Or.inl smallFlipTarget_twoMeet_67_78)
    · right
      left
      rw [smallFlipTarget.twoMeetLevel_comm 6 8 6 7]
      exact smallFlipTarget_twoMeet_67_68
    · left
      simpa using Ordered3Graph.twoMeetLevel_self_eq
        smallFlipTarget 6 8 (by omega)
    · right
      right
      rw [smallFlipTarget_twoMeet_68_78]
      exact smallFlipTarget_twoSplit3
    · right
      left
      rw [smallFlipTarget.twoMeetLevel_comm 7 8 6 7]
      exact smallFlipTarget_twoMeet_67_78
    · right
      right
      rw [smallFlipTarget.twoMeetLevel_comm 7 8 6 8]
      rw [smallFlipTarget_twoMeet_68_78]
      exact smallFlipTarget_twoSplit3
    · left
      simpa using Ordered3Graph.twoMeetLevel_self_eq
        smallFlipTarget 7 8 (by omega)

end DiaryLeafPriority
end ThreeUniformDiaries
