import ThreeUniformDiaries.DiaryFiniteFamilyJointEmbedding
import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface

/-!
# Track B: concrete obstruction to literal initial-segment diary extensions

The empty edge table on the frame [0,4) is a genuine full finite
diary with exactly one nonmarker leaf, namely vertex 3.

In ANY finite full diary having vertex 3 as a genuine leaf, the
exact singleton-meet axiom S1 rules out a second distinct leaf.
For a larger finite frame [0,n) with n>4, role coverage at vertex 4
and the genuine V1/V2 split-witness axioms then give a contradiction.

Thus the four-vertex diary cannot be literally prolonged to a
larger full finite diary while keeping the old first leaf 3 at
the SAME target rank. Protected copies in the already verified
finite-family joint embedding and strong flip-absorber extension
must be allowed to move the old vertices.

This is a finite concrete obstruction to identity-on-prefix
extension, NOT a counterexample to existential protected embedding
or to the full countable-source flip property.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The completely empty edge table on [0,4) is an honest
finite full diary with the single nonmarker leaf at 3. -/
theorem finiteEmptyThree_four_is_finiteDiary :
    FiniteRoleDiaryBlock finiteEmptyThree 4 := by
  have hPred : FiniteRolePrediaryBlock finiteEmptyThree 4 := by
    refine {
      frame := ?_
      role_valid := ?_
      one_split_coherent := ?_
      one_split_witness := ?_
      two_split_coherent := ?_
      two_split_witness := ?_
      leaf_marker_one := ?_
      leaf_marker_two := ?_
      permitted_edge := ?_
    }
    · refine ⟨by omega, ?_⟩
      intro a b c he
      exact False.elim he
    · intro z hz3 hz4
      exact Or.inl ⟨hz3, by intro he; exact he,
        by intro he; exact he⟩
    · intro s a b hs _ha _hb _hsa _hsb
      exact False.elim hs.2.1
    · intro s hs _hsn
      exact False.elim hs.2.1
    · intro s a b c d hs _hab _hcd _ha _hb _hc _hd _habE _hcdE
      exact False.elim hs.2.2
    · intro s hs _hsn
      exact False.elim hs.2.2
    · intro a b hab hbn ha _hb
      have ha3 := ha.1
      omega
    · intro a b hab hbn ha _hb
      have ha3 := ha.1
      omega
    · intro a b c he
      exact False.elim he
  refine ⟨hPred, ?_, ?_⟩
  · intro a b hab hbn ha _hb
    have ha3 := ha.1
    omega
  · intro a b c d hab _hcd hbn _hdn ha _hb _hc _hd
    have ha3 := ha.1
    omega

/-- The genuine sole leaf in the four-vertex finite diary. -/
theorem finiteEmptyThree_leaf_three :
    IsLeaf finiteEmptyThree 3 := by
  exact ⟨by omega, by intro he; exact he,
    by intro he; exact he⟩

/-- A full finite diary containing the leaf 3 cannot contain a
SECOND distinct leaf within its actual finite frame. This is the
bounded, real-frame version of RoleDiary.leaf_three_unique. -/
theorem FiniteRoleDiaryBlock.leaf_three_unique
    {G : Ordered3Graph Nat} {n : Nat}
    (DG : FiniteRoleDiaryBlock G n)
    (hLeaf3 : IsLeaf G 3)
    (b : Nat) (hb : IsLeaf G b) (hbn : b < n) :
    b = 3 := by
  by_cases hb3 : b = 3
  · exact hb3
  · have h3b : 3 < b := by
      have hBound := hb.1
      omega
    have hSplit : IsOneSplit G (G.oneMeetLevel 3 b) :=
      DG.singleton_meets 3 b h3b hbn hLeaf3 hb
    have hMeetCap : G.oneMeetLevel 3 b ≤ 3 :=
      (G.oneMeetLevel_le_min 3 b).trans (min_le_left _ _)
    have hMeet : G.oneMeetLevel 3 b = 3 := by
      have hStart := hSplit.1
      omega
    have hSplit3 : IsOneSplit G 3 := by
      simpa only [hMeet] using hSplit
    exact False.elim (hLeaf3.2.1 hSplit3.2.1)

/-- The four-vertex one-leaf diary is already MAXIMAL for
literal prefix extension: no genuine finite full diary with
more than four frame vertices can keep rank 3 as a leaf.
Split role at 4 would need a later witness leaf, ruled out
by the preceding finite S1 rigidity theorem. -/
theorem FiniteRoleDiaryBlock.leaf_three_forces_bound_four
    {G : Ordered3Graph Nat} {n : Nat}
    (DG : FiniteRoleDiaryBlock G n)
    (hLeaf3 : IsLeaf G 3) :
    n ≤ 4 := by
  by_contra hn
  have h4n : 4 < n := by omega
  rcases DG.prediary.role_valid 4 (by omega) h4n with hLeaf4 | hOne4 | hTwo4
  · have hEq : 4 = 3 :=
      DG.leaf_three_unique hLeaf3 4 hLeaf4 h4n
    omega
  · obtain ⟨a,b,han,hbn,ha,hb,h4a,h4b,hMeet⟩ :=
      DG.prediary.one_split_witness 4 hOne4 h4n
    have ha3 : a = 3 :=
      DG.leaf_three_unique hLeaf3 a ha han
    omega
  · obtain ⟨a,b,c,d,hab,hcd,han,hbn,hcn,hdn,ha,hb,hc,hd,h4a,h4c,hMeet⟩ :=
      DG.prediary.two_split_witness 4 hTwo4 h4n
    have ha3 : a = 3 :=
      DG.leaf_three_unique hLeaf3 a ha han
    omega

/-- Explicit obstruction: no larger finite full diary can
extend the old four-vertex diagram while preserving its
leaf role at the literal position 3. The formulation avoids
pretending that arbitrary finite target copies are
initial-segment embeddings. -/
theorem no_literal_larger_finite_diary_extending_leaf_three
    {G : Ordered3Graph Nat} {n : Nat}
    (hLarge : 4 < n)
    (hLeaf3 : IsLeaf G 3) :
    ¬ FiniteRoleDiaryBlock G n := by
  intro DG
  have hSmall := DG.leaf_three_forces_bound_four hLeaf3
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
