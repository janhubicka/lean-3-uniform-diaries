import ThreeUniformDiaries.DiaryFiniteFirstDisagreementCertificates
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Literal six-vertex source of the small non-rigid absorber

This defines the actual finite ordered ternary graph with edge set
{(0,1,3),(0,3,5),(1,4,5)}, and checks its finite frame, roles,
genuine singleton leaf meet and the V3 orientation directly.

The complete bounded V/E/S certificate is a separate subsequent
step. In particular, a mere explicit edge definition or successful
small Python regression should not be mistaken for a Lean proof of
the full diary axioms.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The explicit 6-vertex one-split/two-leaf source with the
later leaf positive at its unique singleton split. -/
def smallFlipSource : Ordered3Graph Nat where
  edge x y z :=
    (x = 0 ∧ y = 1 ∧ z = 3) ∨
    (x = 0 ∧ y = 3 ∧ z = 5) ∨
    (x = 1 ∧ y = 4 ∧ z = 5)

/-- All genuine small-source edges are increasing triples
entirely contained in its six-vertex frame. -/
theorem smallFlipSource_frame :
    FiniteDiaryEdgeFrame smallFlipSource 6 := by
  refine ⟨by omega, ?_⟩
  intro x y z h
  change (x = 0 ∧ y = 1 ∧ z = 3) ∨
      (x = 0 ∧ y = 3 ∧ z = 5) ∨
      (x = 1 ∧ y = 4 ∧ z = 5) at h
  omega

theorem smallFlipSource_oneSplit3 :
    IsOneSplit smallFlipSource 3 := by
  simp [IsOneSplit, smallFlipSource]

theorem smallFlipSource_leaf4 :
    IsLeaf smallFlipSource 4 := by
  simp [IsLeaf, smallFlipSource]

theorem smallFlipSource_leaf5 :
    IsLeaf smallFlipSource 5 := by
  simp [IsLeaf, smallFlipSource]

/-- No genuine two-split can occur in this source; marker-2
role edges are absent at every target vertex. -/
theorem smallFlipSource_no_twoSplit (s : Nat) :
    ¬ IsTwoSplit smallFlipSource s := by
  intro hs
  have he := hs.2.2
  simp [smallFlipSource] at he

/-- The unique vertex of role one-split is source vertex 3. -/
theorem smallFlipSource_oneSplit_eq_three
    {s : Nat} (hs : IsOneSplit smallFlipSource s) :
    s = 3 := by
  have he := hs.2.1
  simp [smallFlipSource] at he
  omega

/-- The E1--E5 permitted-edge property holds on the actual
finite edge set, not merely the abstract role sequence. -/
theorem smallFlipSource_permitted :
    ∀ x y z : Nat,
      smallFlipSource.edge x y z →
      PermittedDiaryEdge smallFlipSource x y z := by
  intro x y z he
  change (x = 0 ∧ y = 1 ∧ z = 3) ∨
      (x = 0 ∧ y = 3 ∧ z = 5) ∨
      (x = 1 ∧ y = 4 ∧ z = 5) at he
  rcases he with ⟨rfl,rfl,rfl⟩ |
      ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact Or.inl ⟨rfl,Or.inl rfl,by omega⟩
  · exact Or.inr (Or.inl
      ⟨rfl,smallFlipSource_oneSplit3,smallFlipSource_leaf5⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Or.inl rfl,smallFlipSource_leaf4,smallFlipSource_leaf5⟩)))

/-- Below cut 3 the two genuine source leaf singleton types
agree: all their earlier possible edge tests are absent. -/
theorem smallFlipSource_leaf_oneType_at_three :
    smallFlipSource.SameOneTypeBelow 3 4 5 := by
  intro x y hxy hy3
  have h4 : ¬ smallFlipSource.edge x y 4 := by
    simp [smallFlipSource]
  have h5 : ¬ smallFlipSource.edge x y 5 := by
    simp [smallFlipSource]
    omega
  exact iff_of_false h4 h5

/-- The unique source leaf meet is exactly 3, witnessed by
the changed (0,3,4)/(0,3,5) E2 bit. -/
theorem smallFlipSource_leaf_meet :
    smallFlipSource.oneMeetLevel 4 5 = 3 := by
  apply Ordered3Graph.oneMeetLevel_eq_of_first_disagreement
    smallFlipSource 4 5 3 (by omega)
    smallFlipSource_leaf_oneType_at_three
  refine ⟨0,by omega,?_⟩
  simp [smallFlipSource]

/-- Literal V3 comparison for the sole source leaf pair. -/
theorem smallFlipSource_lex45 :
    LexEarlier smallFlipSource 4 5 := by
  have h := E_oneSplit_lexEarlier_iff_right
    smallFlipSource_permitted
    3 4 5 smallFlipSource_oneSplit3
    (by omega) (by omega) smallFlipSource_leaf_meet
  apply h.mpr
  simp [smallFlipSource]

/-- Self-comparison of an ordered full two-type is capped at
its first leaf, for ANY ordered three-graph. -/
theorem Ordered3Graph.twoMeetLevel_self_eq
    (H : Ordered3Graph Nat) (a b : Nat) (hab : a < b) :
    H.twoMeetLevel a b a b = a := by
  have hu : H.twoMeetLevel a b a b ≤ a := by
    have h := H.twoMeetLevel_le_min a b a b
    simpa using h
  have hAgree : H.SameTwoTypeBelow a a b a b := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      exact Iff.rfl
    · intro x y hxy hy
      exact Iff.rfl
    · intro x hx
      exact Iff.rfl
  have hl : a ≤ H.twoMeetLevel a b a b := by
    apply Nat.le_findGreatest (by simp)
    exact hAgree
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
