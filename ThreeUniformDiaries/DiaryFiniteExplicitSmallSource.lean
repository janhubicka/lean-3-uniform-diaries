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
  classical
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



/-- The only leaves in the bounded six-vertex frame are 4 and 5. -/
theorem smallFlipSource_leaf_iff
    (z : Nat) (hz3 : 3 ≤ z) (hz6 : z < 6) :
    IsLeaf smallFlipSource z ↔ (z = 4 ∨ z = 5) := by
  constructor
  · intro hz
    have hn3 : z ≠ 3 := by
      intro heq
      subst z
      exact hz.2.1 smallFlipSource_oneSplit3.2.1
    omega
  · rintro (rfl | rfl)
    · exact smallFlipSource_leaf4
    · exact smallFlipSource_leaf5

/-- This source has the full actual bounded finite V/E/S diary
axioms. The only 1-split witness is (4,5), the E3 witness
conditions are vacuous, V3 is the positive right branch
comparison, and S2 is the first-leaf self-cap. -/
theorem smallFlipSource_is_finiteDiary :
    FiniteRoleDiaryBlock smallFlipSource 6 := by
  refine {
    prediary := {
      frame := smallFlipSource_frame
      role_valid := ?_
      one_split_coherent := ?_
      one_split_witness := ?_
      two_split_coherent := ?_
      two_split_witness := ?_
      leaf_marker_one := ?_
      leaf_marker_two := ?_
      permitted_edge := smallFlipSource_permitted
    }
    singleton_meets := ?_
    pair_meets := ?_
  }
  · intro z hz3 hz6
    have hz : z = 3 ∨ z = 4 ∨ z = 5 := by omega
    rcases hz with rfl | rfl | rfl
    · exact Or.inr (Or.inl smallFlipSource_oneSplit3)
    · exact Or.inl smallFlipSource_leaf4
    · exact Or.inl smallFlipSource_leaf5
  · intro s a b hs _ha _hb hsa hsb
    have h3 : s = 3 := smallFlipSource_oneSplit_eq_three hs
    subst s
    have ha5 : a = 5 := by
      simpa [smallFlipSource] using hsa
    have hb5 : b = 5 := by
      simpa [smallFlipSource] using hsb
    subst a
    subst b
    intro x y _ _
    exact Iff.rfl
  · intro s hs _hsk
    have h3 : s = 3 := smallFlipSource_oneSplit_eq_three hs
    subst s
    refine ⟨4,5,by omega,by omega,
      smallFlipSource_leaf4,smallFlipSource_leaf5,
      by omega,by omega,?_⟩
    exact smallFlipSource_leaf_meet
  · intro s a b c d hs _hab _hcd _ha _hb _hc _hd _habPos _hcdPos
    exact (smallFlipSource_no_twoSplit s hs).elim
  · intro s hs _hsk
    exact (smallFlipSource_no_twoSplit s hs).elim
  · intro a b hab hb ha hbLeaf
    have haCases := (smallFlipSource_leaf_iff
      a ha.1 (by omega)).mp ha
    have hbCases := (smallFlipSource_leaf_iff
      b hbLeaf.1 hb).mp hbLeaf
    have ha4 : a = 4 := by omega
    have hb5 : b = 5 := by omega
    subst a
    subst b
    simp [smallFlipSource,smallFlipSource_lex45]
  · intro a b hab hb ha hbLeaf
    have haCases := (smallFlipSource_leaf_iff
      a ha.1 (by omega)).mp ha
    have hbCases := (smallFlipSource_leaf_iff
      b hbLeaf.1 hb).mp hbLeaf
    have ha4 : a = 4 := by omega
    have hb5 : b = 5 := by omega
    subst a
    subst b
    simp [smallFlipSource,smallFlipSource_lex45]
  · intro a b hab hb ha hbLeaf
    have haCases := (smallFlipSource_leaf_iff
      a ha.1 (by omega)).mp ha
    have hbCases := (smallFlipSource_leaf_iff
      b hbLeaf.1 hb).mp hbLeaf
    have ha4 : a = 4 := by omega
    have hb5 : b = 5 := by omega
    subst a
    subst b
    rw [smallFlipSource_leaf_meet]
    exact smallFlipSource_oneSplit3
  · intro a b c d hab hcd hb hd ha hbLeaf hc hdLeaf
    have haCases := (smallFlipSource_leaf_iff
      a ha.1 (by omega)).mp ha
    have hbCases := (smallFlipSource_leaf_iff
      b hbLeaf.1 hb).mp hbLeaf
    have hcCases := (smallFlipSource_leaf_iff
      c hc.1 (by omega)).mp hc
    have hdCases := (smallFlipSource_leaf_iff
      d hdLeaf.1 hd).mp hdLeaf
    have ha4 : a = 4 := by omega
    have hb5 : b = 5 := by omega
    have hc4 : c = 4 := by omega
    have hd5 : d = 5 := by omega
    subst a
    subst b
    subst c
    subst d
    left
    exact Ordered3Graph.twoMeetLevel_self_eq
      smallFlipSource 4 5 (by omega)

end DiaryLeafPriority
end ThreeUniformDiaries
