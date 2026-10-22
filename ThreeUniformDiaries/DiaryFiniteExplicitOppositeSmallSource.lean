import ThreeUniformDiaries.DiaryFiniteExplicitSmallSource
import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# The small six-vertex diary is genuinely non-rigid under flips

The companion to smallFlipSource changes both the positive 1-split
branch and the V3 leaf-pair marker, preserving all numerical
leaf singleton and pair meets. Its literal edge set is
{(0,1,3),(0,3,4),(2,4,5)}.

We prove both its COMPLETE bounded V/E/S diary structure and
that the identity is a true diary flip from smallFlipSource,
not just a difference of two arbitrary Boolean edge tables.
Thus the small absorber example is *provably* non-rigid.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

def smallFlipSourceOpposite : Ordered3Graph Nat where
  edge x y z :=
    (x = 0 ∧ y = 1 ∧ z = 3) ∨
    (x = 0 ∧ y = 3 ∧ z = 4) ∨
    (x = 2 ∧ y = 4 ∧ z = 5)

theorem smallFlipSourceOpposite_frame :
    FiniteDiaryEdgeFrame smallFlipSourceOpposite 6 := by
  refine ⟨by omega,?_⟩
  intro x y z h
  change (x=0 ∧ y=1 ∧ z=3) ∨
    (x=0 ∧ y=3 ∧ z=4) ∨
    (x=2 ∧ y=4 ∧ z=5) at h
  omega

theorem smallFlipSourceOpposite_oneSplit3 :
    IsOneSplit smallFlipSourceOpposite 3 := by
  simp [IsOneSplit,smallFlipSourceOpposite]
theorem smallFlipSourceOpposite_leaf4 :
    IsLeaf smallFlipSourceOpposite 4 := by
  simp [IsLeaf,smallFlipSourceOpposite]
theorem smallFlipSourceOpposite_leaf5 :
    IsLeaf smallFlipSourceOpposite 5 := by
  simp [IsLeaf,smallFlipSourceOpposite]

theorem smallFlipSourceOpposite_no_twoSplit (s : Nat) :
    ¬ IsTwoSplit smallFlipSourceOpposite s := by
  intro hs
  have he := hs.2.2
  simp [smallFlipSourceOpposite] at he

theorem smallFlipSourceOpposite_oneSplit_eq_three
    {s : Nat} (hs : IsOneSplit smallFlipSourceOpposite s) :
    s = 3 := by
  have he := hs.2.1
  simp [smallFlipSourceOpposite] at he
  omega

theorem smallFlipSourceOpposite_permitted :
    ∀ x y z : Nat,
      smallFlipSourceOpposite.edge x y z →
      PermittedDiaryEdge smallFlipSourceOpposite x y z := by
  intro x y z he
  change (x=0 ∧ y=1 ∧ z=3) ∨
    (x=0 ∧ y=3 ∧ z=4) ∨
    (x=2 ∧ y=4 ∧ z=5) at he
  rcases he with ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact Or.inl ⟨rfl,Or.inl rfl,by omega⟩
  · exact Or.inr (Or.inl
      ⟨rfl,smallFlipSourceOpposite_oneSplit3,
        smallFlipSourceOpposite_leaf4⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Or.inr rfl,smallFlipSourceOpposite_leaf4,
        smallFlipSourceOpposite_leaf5⟩)))

theorem smallFlipSourceOpposite_leaf_oneType_at_three :
    smallFlipSourceOpposite.SameOneTypeBelow 3 4 5 := by
  intro x y hxy hy3
  have h4 : ¬ smallFlipSourceOpposite.edge x y 4 := by
    simp [smallFlipSourceOpposite]
    omega
  have h5 : ¬ smallFlipSourceOpposite.edge x y 5 := by
    simp [smallFlipSourceOpposite]
    omega
  exact iff_of_false h4 h5

theorem smallFlipSourceOpposite_leaf_meet :
    smallFlipSourceOpposite.oneMeetLevel 4 5 = 3 := by
  apply Ordered3Graph.oneMeetLevel_eq_of_first_disagreement
    smallFlipSourceOpposite 4 5 3 (by omega)
    smallFlipSourceOpposite_leaf_oneType_at_three
  exact ⟨0,by omega,by simp [smallFlipSourceOpposite]⟩

theorem smallFlipSourceOpposite_not_lex45 :
    ¬ LexEarlier smallFlipSourceOpposite 4 5 := by
  intro h
  have hRight :=
    (E_oneSplit_lexEarlier_iff_right
      smallFlipSourceOpposite_permitted
      3 4 5 smallFlipSourceOpposite_oneSplit3
      (by omega) (by omega)
      smallFlipSourceOpposite_leaf_meet).mp h
  simp [smallFlipSourceOpposite] at hRight

theorem smallFlipSourceOpposite_leaf_iff
    (z : Nat) (hz3 : 3 ≤ z) (hz6 : z < 6) :
    IsLeaf smallFlipSourceOpposite z ↔ (z = 4 ∨ z = 5) := by
  constructor
  · intro hz
    have hn3 : z ≠ 3 := by
      intro heq
      subst z
      exact hz.2.1 smallFlipSourceOpposite_oneSplit3.2.1
    omega
  · rintro (rfl | rfl)
    · exact smallFlipSourceOpposite_leaf4
    · exact smallFlipSourceOpposite_leaf5

theorem smallFlipSourceOpposite_is_finiteDiary :
    FiniteRoleDiaryBlock smallFlipSourceOpposite 6 := by
  refine {
    prediary := {
      frame := smallFlipSourceOpposite_frame
      role_valid := ?_
      one_split_coherent := ?_
      one_split_witness := ?_
      two_split_coherent := ?_
      two_split_witness := ?_
      leaf_marker_one := ?_
      leaf_marker_two := ?_
      permitted_edge := smallFlipSourceOpposite_permitted
    }
    singleton_meets := ?_
    pair_meets := ?_
  }
  · intro z hz3 hz6
    have hz : z=3 ∨ z=4 ∨ z=5 := by omega
    rcases hz with rfl | rfl | rfl
    · exact Or.inr (Or.inl smallFlipSourceOpposite_oneSplit3)
    · exact Or.inl smallFlipSourceOpposite_leaf4
    · exact Or.inl smallFlipSourceOpposite_leaf5
  · intro s a b hs _ha _hb hsa hsb
    have h3 : s=3 := smallFlipSourceOpposite_oneSplit_eq_three hs
    subst s
    have ha4 : a=4 := by simpa [smallFlipSourceOpposite] using hsa
    have hb4 : b=4 := by simpa [smallFlipSourceOpposite] using hsb
    subst a
    subst b
    intro x y _ _
    exact Iff.rfl
  · intro s hs _hsk
    have h3 : s=3 := smallFlipSourceOpposite_oneSplit_eq_three hs
    subst s
    exact ⟨4,5,by omega,by omega,
      smallFlipSourceOpposite_leaf4,smallFlipSourceOpposite_leaf5,
      by omega,by omega,smallFlipSourceOpposite_leaf_meet⟩
  · intro s a b c d hs _hab _hcd _ha _hb _hc _hd _habPos _hcdPos
    exact (smallFlipSourceOpposite_no_twoSplit s hs).elim
  · intro s hs _hsk
    exact (smallFlipSourceOpposite_no_twoSplit s hs).elim
  · intro a b hab hb ha hbLeaf
    have haCases := (smallFlipSourceOpposite_leaf_iff
      a ha.1 (by omega)).mp ha
    have hbCases := (smallFlipSourceOpposite_leaf_iff
      b hbLeaf.1 hb).mp hbLeaf
    have ha4 : a=4 := by omega
    have hb5 : b=5 := by omega
    subst a
    subst b
    change smallFlipSourceOpposite.edge 1 4 5 ↔
      LexEarlier smallFlipSourceOpposite 4 5
    exact iff_of_false (by simp [smallFlipSourceOpposite])
      smallFlipSourceOpposite_not_lex45
  · intro a b hab hb ha hbLeaf
    have haCases := (smallFlipSourceOpposite_leaf_iff
      a ha.1 (by omega)).mp ha
    have hbCases := (smallFlipSourceOpposite_leaf_iff
      b hbLeaf.1 hb).mp hbLeaf
    have ha4 : a=4 := by omega
    have hb5 : b=5 := by omega
    subst a
    subst b
    change smallFlipSourceOpposite.edge 2 4 5 ↔
      ¬ LexEarlier smallFlipSourceOpposite 4 5
    exact iff_of_true (by simp [smallFlipSourceOpposite])
      smallFlipSourceOpposite_not_lex45
  · intro a b hab hb ha hbLeaf
    have haCases := (smallFlipSourceOpposite_leaf_iff
      a ha.1 (by omega)).mp ha
    have hbCases := (smallFlipSourceOpposite_leaf_iff
      b hbLeaf.1 hb).mp hbLeaf
    have ha4 : a=4 := by omega
    have hb5 : b=5 := by omega
    subst a
    subst b
    rw [smallFlipSourceOpposite_leaf_meet]
    exact smallFlipSourceOpposite_oneSplit3
  · intro a b c d hab hcd hb hd ha hbLeaf hc hdLeaf
    have haCases := (smallFlipSourceOpposite_leaf_iff
      a ha.1 (by omega)).mp ha
    have hbCases := (smallFlipSourceOpposite_leaf_iff
      b hbLeaf.1 hb).mp hbLeaf
    have hcCases := (smallFlipSourceOpposite_leaf_iff
      c hc.1 (by omega)).mp hc
    have hdCases := (smallFlipSourceOpposite_leaf_iff
      d hdLeaf.1 hd).mp hdLeaf
    have ha4 : a=4 := by omega
    have hb5 : b=5 := by omega
    have hc4 : c=4 := by omega
    have hd5 : d=5 := by omega
    subst a
    subst b
    subst c
    subst d
    left
    exact Ordered3Graph.twoMeetLevel_self_eq
      smallFlipSourceOpposite 4 5 (by omega)

/-- The two six-vertex diaries have exactly the same roles,
no all-leaf triple, and the same genuine leaf meets. -/
private theorem oneMeetLevel_self_for_small_flip
    (H : Ordered3Graph Nat) (a : Nat) :
    H.oneMeetLevel a a = a := by
  classical
  have hUpper : H.oneMeetLevel a a ≤ a := by
    have h := H.oneMeetLevel_le_min a a
    simpa using h
  have hAgree : H.SameOneTypeBelow a a a := by
    intro x y hxy hy
    exact Iff.rfl
  have hLower : a ≤ H.oneMeetLevel a a :=
    Nat.le_findGreatest (by simp) hAgree
  omega

theorem smallFlipSourceOpposite_is_sourceFlip :
    FiniteDiaryFlip smallFlipSource smallFlipSourceOpposite 6 := by
  refine {
    source_diary := smallFlipSource_is_finiteDiary
    target_diary := smallFlipSourceOpposite_is_finiteDiary
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u hu3 hu6
    have hCases : u=3 ∨ u=4 ∨ u=5 := by omega
    rcases hCases with rfl | rfl | rfl <;>
      simp [IsLeaf,IsOneSplit,IsTwoSplit,
        smallFlipSource,smallFlipSourceOpposite]
  · intro a b c hab hbc hc6 ha hb hc
    have ha6 : a<6 := by omega
    have hb6 : b<6 := by omega
    have haC := (smallFlipSource_leaf_iff a ha.1 ha6).mp ha
    have hbC := (smallFlipSource_leaf_iff b hb.1 hb6).mp hb
    omega
  · intro a b ha6 hb6 ha hb
    have haC := (smallFlipSource_leaf_iff
      a ha.1 ha6).mp ha
    have hbC := (smallFlipSource_leaf_iff
      b hb.1 hb6).mp hb
    rcases haC with rfl | rfl <;> rcases hbC with rfl | rfl
    · simp [oneMeetLevel_self_for_small_flip]
    · exact smallFlipSource_leaf_meet.trans
        smallFlipSourceOpposite_leaf_meet.symm
    · calc
        smallFlipSource.oneMeetLevel 5 4 =
            smallFlipSource.oneMeetLevel 4 5 :=
          finiteLeafMeet_oneMeet_comm smallFlipSource 5 4
        _ = 3 := smallFlipSource_leaf_meet
        _ = smallFlipSourceOpposite.oneMeetLevel 4 5 :=
          smallFlipSourceOpposite_leaf_meet.symm
        _ = smallFlipSourceOpposite.oneMeetLevel 5 4 :=
          (finiteLeafMeet_oneMeet_comm smallFlipSourceOpposite 5 4).symm
    · simp [oneMeetLevel_self_for_small_flip]
  · intro a b c d hab hcd hb6 hd6 ha hb hc hd
    have haC := (smallFlipSource_leaf_iff
      a ha.1 (by omega)).mp ha
    have hbC := (smallFlipSource_leaf_iff
      b hb.1 hb6).mp hb
    have hcC := (smallFlipSource_leaf_iff
      c hc.1 (by omega)).mp hc
    have hdC := (smallFlipSource_leaf_iff
      d hd.1 hd6).mp hd
    have ha4 : a=4 := by omega
    have hb5 : b=5 := by omega
    have hc4 : c=4 := by omega
    have hd5 : d=5 := by omega
    subst a; subst b; subst c; subst d
    rw [Ordered3Graph.twoMeetLevel_self_eq
      smallFlipSource 4 5 (by omega),
      Ordered3Graph.twoMeetLevel_self_eq
      smallFlipSourceOpposite 4 5 (by omega)]

theorem smallFlipSourceOpposite_ne :
    smallFlipSourceOpposite ≠ smallFlipSource := by
  intro h
  have hBit := congrArg
    (fun H : Ordered3Graph Nat => H.edge 0 3 5) h
  have hNo : ¬ smallFlipSourceOpposite.edge 0 3 5 := by
    simp [smallFlipSourceOpposite]
  have hYes : smallFlipSource.edge 0 3 5 := by
    simp [smallFlipSource]
  exact hNo (hBit.symm ▸ hYes)

end DiaryLeafPriority
end ThreeUniformDiaries
