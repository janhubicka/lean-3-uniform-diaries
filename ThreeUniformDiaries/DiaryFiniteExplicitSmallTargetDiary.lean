import ThreeUniformDiaries.DiaryFiniteExplicitSmallTarget
import ThreeUniformDiaries.DiaryFiniteFirstDisagreementCertificates

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
  · exact Or.inl ⟨rfl,Or.inr (Or.inl rfl),by omega⟩
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

end DiaryLeafPriority
end ThreeUniformDiaries
