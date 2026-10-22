import ThreeUniformDiaries.DiaryFiniteExplicitSmallSource

/-!
# Literal nine-vertex target of the small non-rigid flip absorber

The target has one 2-split at 3, two 1-splits at 4,5 and
leaves 6,7,8. Its TEN edges are explicitly listed below.

This first module checks the bounded frame, marker roles and
the exact singleton leaf meets (6,7)=4, (7,8)=4,
(6,8)=5. The auxiliary full pair-meet certificate
(6,8) wedge (7,8)=3 is also included.

These statements are derived directly from literal triples and
the finite first-disagreement certificates, rather than
introducing numerical meet values as axioms.
The complete finite V/E/S target diary and every-target-flip
absorbing-copy theorem require further verification.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

def smallFlipTarget : Ordered3Graph Nat where
  edge x y z :=
    (x = 0 ∧ y = 2 ∧ z = 3) ∨
    (x = 0 ∧ y = 1 ∧ z = 4) ∨
    (x = 0 ∧ y = 1 ∧ z = 5) ∨
    (x = 0 ∧ y = 4 ∧ z = 6) ∨
    (x = 0 ∧ y = 4 ∧ z = 8) ∨
    (x = 0 ∧ y = 5 ∧ z = 8) ∨
    (x = 2 ∧ y = 6 ∧ z = 7) ∨
    (x = 1 ∧ y = 6 ∧ z = 8) ∨
    (x = 1 ∧ y = 7 ∧ z = 8) ∨
    (x = 3 ∧ y = 6 ∧ z = 8)

/-- There are no artificial edges outside the actual nine-vertex
target interval or on non-increasing triples. -/
theorem smallFlipTarget_frame :
    FiniteDiaryEdgeFrame smallFlipTarget 9 := by
  refine ⟨by omega, ?_⟩
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
  omega

theorem smallFlipTarget_twoSplit3 :
    IsTwoSplit smallFlipTarget 3 := by
  simp [IsTwoSplit, smallFlipTarget]

theorem smallFlipTarget_oneSplit4 :
    IsOneSplit smallFlipTarget 4 := by
  simp [IsOneSplit, smallFlipTarget]

theorem smallFlipTarget_oneSplit5 :
    IsOneSplit smallFlipTarget 5 := by
  simp [IsOneSplit, smallFlipTarget]

theorem smallFlipTarget_leaf6 :
    IsLeaf smallFlipTarget 6 := by
  simp [IsLeaf, smallFlipTarget]

theorem smallFlipTarget_leaf7 :
    IsLeaf smallFlipTarget 7 := by
  simp [IsLeaf, smallFlipTarget]

theorem smallFlipTarget_leaf8 :
    IsLeaf smallFlipTarget 8 := by
  simp [IsLeaf, smallFlipTarget]

/-- The only target 2-split is vertex 3. -/
theorem smallFlipTarget_twoSplit_eq_three
    {s : Nat} (hs : IsTwoSplit smallFlipTarget s) :
    s = 3 := by
  have he := hs.2.2
  simp [smallFlipTarget] at he
  omega

/-- The two target 1-splits are exactly vertices 4 and 5. -/
theorem smallFlipTarget_oneSplit_eq_four_or_five
    {s : Nat} (hs : IsOneSplit smallFlipTarget s) :
    s = 4 ∨ s = 5 := by
  have he := hs.2.1
  simp [smallFlipTarget] at he
  omega

/-- The three leaves share no singleton tests below cut 4.
In particular each of (6,7) and (7,8) first separates
at the next 1-split edge coordinate. -/
theorem smallFlipTarget_oneType_6_7_at_four :
    smallFlipTarget.SameOneTypeBelow 4 6 7 := by
  intro x y hxy hy
  have h6 : ¬ smallFlipTarget.edge x y 6 := by
    simp [smallFlipTarget]
    omega
  have h7 : ¬ smallFlipTarget.edge x y 7 := by
    simp [smallFlipTarget]
    omega
  exact iff_of_false h6 h7

theorem smallFlipTarget_oneType_7_8_at_four :
    smallFlipTarget.SameOneTypeBelow 4 7 8 := by
  intro x y hxy hy
  have h7 : ¬ smallFlipTarget.edge x y 7 := by
    simp [smallFlipTarget]
    omega
  have h8 : ¬ smallFlipTarget.edge x y 8 := by
    simp [smallFlipTarget]
    omega
  exact iff_of_false h7 h8

theorem smallFlipTarget_oneType_6_8_at_five :
    smallFlipTarget.SameOneTypeBelow 5 6 8 := by
  intro x y hxy hy
  simp [smallFlipTarget]
  omega

theorem smallFlipTarget_meet_6_7 :
    smallFlipTarget.oneMeetLevel 6 7 = 4 := by
  apply Ordered3Graph.oneMeetLevel_eq_of_first_disagreement
    smallFlipTarget 6 7 4 (by omega)
    smallFlipTarget_oneType_6_7_at_four
  exact ⟨0,by omega,by simp [smallFlipTarget]⟩

theorem smallFlipTarget_meet_7_8 :
    smallFlipTarget.oneMeetLevel 7 8 = 4 := by
  apply Ordered3Graph.oneMeetLevel_eq_of_first_disagreement
    smallFlipTarget 7 8 4 (by omega)
    smallFlipTarget_oneType_7_8_at_four
  exact ⟨0,by omega,by simp [smallFlipTarget]⟩

theorem smallFlipTarget_meet_6_8 :
    smallFlipTarget.oneMeetLevel 6 8 = 5 := by
  apply Ordered3Graph.oneMeetLevel_eq_of_first_disagreement
    smallFlipTarget 6 8 5 (by omega)
    smallFlipTarget_oneType_6_8_at_five
  exact ⟨0,by omega,by simp [smallFlipTarget]⟩

/-- The two ordered pairs (6,8) and (7,8) have full type
meet exactly at 2-split vertex 3. Their auxiliary incidences
agree through all three markers and differ at edge (3,6,8). -/
theorem smallFlipTarget_twoType_68_78_at_three :
    smallFlipTarget.SameTwoTypeBelow 3 6 8 7 8 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    exact smallFlipTarget_oneType_6_7_at_four hxy (by omega)
  · intro x y hxy hy
    exact Iff.rfl
  · intro x hx
    simp [smallFlipTarget]
    omega

theorem smallFlipTarget_twoMeet_68_78 :
    smallFlipTarget.twoMeetLevel 6 8 7 8 = 3 := by
  apply Ordered3Graph.twoMeetLevel_eq_of_aux_first_disagreement
    smallFlipTarget 6 8 7 8 3 (by omega)
    smallFlipTarget_twoType_68_78_at_three
  simp [smallFlipTarget]

end DiaryLeafPriority
end ThreeUniformDiaries
