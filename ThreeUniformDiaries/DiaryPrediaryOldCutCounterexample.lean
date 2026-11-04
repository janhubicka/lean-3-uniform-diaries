import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.ExactTypeMeetLevels

/-!
# Track B: explicit five-vertex counterexample to printed old-cut preservation

The printed pre-diary completion lemma asserts that an old singleton
type equality at a cut is preserved in the completed diary. This is
FALSE, even for a genuine five-vertex finite V/E pre-diary.

The source has vertices 0,...,4 and its sole edge is (1,3,4).
The genuine leaves are 3 and 4. Their singleton types agree through
source cut 3, since the only edge with third coordinate 4 has middle
coordinate 3. The Devlin marker-1 edge is legitimate: the first
singleton meet is capped at 3 and its true LexEarlier(3,4) is true.

In EVERY complete diary, S1 forces the first singleton meet of
distinct leaves to be a one-split, not the earlier leaf. Thus those
leaf types cannot agree through the cut at the first leaf. No
strictly increasing, role-preserving completion can preserve the
printed old-cut clause at the source pair (3,4).

This does NOT contradict the independently validated existence of
a diary with the original graph as its complete induced leaf reduct:
that construction intentionally does not preserve this false
stronger condition.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The finite five-vertex pre-diary, with only the Devlin edge
(1,3,4) in the finite frame. It is intentionally zero-extended on
Nat; the finite pre-diary predicate is bounded by 5. -/
def oldCutFiveVertexPrediary : Ordered3Graph Nat where
  edge x y z := x = 1 ∧ y = 3 ∧ z = 4

private theorem oldCutFiveVertex_isLeaf (z : Nat) (hz : 3 ≤ z) :
    IsLeaf oldCutFiveVertexPrediary z := by
  refine ⟨hz, ?_, ?_⟩ <;> simp [oldCutFiveVertexPrediary]

/-- The two genuine source leaves agree in all singleton tests whose
middle coordinate is strictly below 3. -/
theorem oldCutFiveVertex_sameOneBelowThree :
    oldCutFiveVertexPrediary.SameOneTypeBelow 3 3 4 := by
  intro x y hxy hy
  have hne : y ≠ 3 := by omega
  simp [oldCutFiveVertexPrediary, hne]

private theorem oldCutFiveVertex_oneMeet :
    oldCutFiveVertexPrediary.oneMeetLevel 3 4 = 3 := by
  classical
  apply Nat.le_antisymm
  · have h := oldCutFiveVertexPrediary.oneMeetLevel_le_min 3 4
    omega
  · apply Nat.le_findGreatest (by omega)
    exact oldCutFiveVertex_sameOneBelowThree

private theorem oldCutFiveVertex_lex :
    LexEarlier oldCutFiveVertexPrediary 3 4 :=
  Or.inl ⟨by omega, oldCutFiveVertex_oneMeet⟩

/-- This example satisfies the ACTUAL finite V/E pre-diary axioms,
including its true Devlin comparison. It fails S1, as it should. -/
theorem oldCutFiveVertex_is_finitePrediary :
    FiniteRolePrediaryBlock oldCutFiveVertexPrediary 5 := by
  have noOne : ∀ z, ¬ IsOneSplit oldCutFiveVertexPrediary z := by
    intro z
    simp [IsOneSplit, oldCutFiveVertexPrediary]
  have noTwo : ∀ z, ¬ IsTwoSplit oldCutFiveVertexPrediary z := by
    intro z
    simp [IsTwoSplit, oldCutFiveVertexPrediary]
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
    intro x y z he
    change x = 1 ∧ y = 3 ∧ z = 4 at he
    rcases he with ⟨rfl, rfl, rfl⟩
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro z hz _
    exact Or.inl (oldCutFiveVertex_isLeaf z hz)
  · intro s _ _ hs
    exact False.elim (noOne s hs)
  · intro s hs
    exact False.elim (noOne s hs)
  · intro s _ _ _ _ hs
    exact False.elim (noTwo s hs)
  · intro s hs
    exact False.elim (noTwo s hs)
  · intro a b hab hb ha hbLeaf
    have ha3 : 3 ≤ a := ha.1
    have heqa : a = 3 := by omega
    have heqb : b = 4 := by omega
    subst a
    subst b
    constructor
    · intro _
      exact oldCutFiveVertex_lex
    · intro _
      simp [oldCutFiveVertexPrediary]
  · intro a b hab hb ha hbLeaf
    have ha3 : 3 ≤ a := ha.1
    have heqa : a = 3 := by omega
    have heqb : b = 4 := by omega
    subst a
    subst b
    constructor
    · intro he
      have hf : False := by simpa [oldCutFiveVertexPrediary] using he
      exact False.elim hf
    · intro hn
      exact False.elim (hn oldCutFiveVertex_lex)
  · intro x y z he
    change x = 1 ∧ y = 3 ∧ z = 4 at he
    rcases he with ⟨rfl, rfl, rfl⟩
    unfold PermittedDiaryEdge
    exact Or.inr (Or.inr (Or.inr
      (Or.inl ⟨Or.inl rfl,
        oldCutFiveVertex_isLeaf 3 (by omega),
        oldCutFiveVertex_isLeaf 4 (by omega)⟩)))

/-- Algebraic heart of the obstruction: if S1 makes the numerical
meet of a,b a one-split, their singleton columns cannot agree all
the way through the first leaf a. No V/E properties are needed. -/
theorem not_same_one_at_first_of_oneSplitMeet
    (K : Ordered3Graph Nat) (a b : Nat)
    (hab : a < b) (ha : IsLeaf K a)
    (hSplit : IsOneSplit K (K.oneMeetLevel a b)) :
    ¬ K.SameOneTypeBelow a a b := by
  classical
  intro hs
  have hUpper : K.oneMeetLevel a b ≤ a := by
    have h := K.oneMeetLevel_le_min a b
    omega
  have hLower : a ≤ K.oneMeetLevel a b := by
    apply Nat.le_findGreatest (by omega)
    exact hs
  have hEq : K.oneMeetLevel a b = a := by omega
  have hOne : IsOneSplit K a := by
    simpa only [hEq] using hSplit
  exact ha.2.1 hOne.2.1

/-- Every two distinct genuine leaves of a complete diary disagree
as singleton types before the cut at the earlier leaf. -/
theorem RoleDiary.distinct_leaves_not_same_one_at_first
    {K : Ordered3Graph Nat} (D : RoleDiary K)
    (a b : Nat) (hab : a < b)
    (ha : IsLeaf K a) (hb : IsLeaf K b) :
    ¬ K.SameOneTypeBelow a a b := by
  exact not_same_one_at_first_of_oneSplitMeet K a b hab ha
    (D.singleton_meets a b ha hb (by omega))

/-- The same obstruction holds within a genuinely finite complete
diary block, without relying on its artificial Nat tail. -/
theorem FiniteRoleDiaryBlock.distinct_leaves_not_same_one_at_first
    {K : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock K n)
    (a b : Nat) (hab : a < b) (hb : b < n)
    (ha : IsLeaf K a) (hLeafB : IsLeaf K b) :
    ¬ K.SameOneTypeBelow a a b := by
  exact not_same_one_at_first_of_oneSplitMeet K a b hab ha
    (D.singleton_meets a b hab hb ha hLeafB)

/-- The printed cut-preservation clause is unachievable at the
concrete five-vertex pre-diary. Even for a genuinely finite full
target and a strictly increasing map that sends the two source
leaves to target leaves, source agreement through 3 cannot imply
target agreement through the image of 3. -/
theorem oldCutFiveVertex_no_finite_preserving_completion
    {K : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock K n)
    (f : Nat → Nat) (hf : StrictMono f)
    (hf4 : f 4 < n)
    (h3 : IsLeaf K (f 3)) (h4 : IsLeaf K (f 4)) :
    ¬ (oldCutFiveVertexPrediary.SameOneTypeBelow 3 3 4 →
       K.SameOneTypeBelow (f 3) (f 3) (f 4)) := by
  intro hPreserve
  exact D.distinct_leaves_not_same_one_at_first
    (f 3) (f 4) (hf (by omega)) hf4 h3 h4
    (hPreserve oldCutFiveVertex_sameOneBelowThree)


/-- The literal manuscript-strength contradiction: even assuming
the finite embedding fixes all three markers and preserves/refects
ALL source triples below five, its two leaf images must be true
target leaves. The false old-cut clause would then violate S1.

The hypothesis tests only source vertices < 5; no artificial
zero-extended source tail is ever treated as part of the finite
pre-diary. -/
theorem oldCutFiveVertex_no_markerFixed_induced_oldCut_completion
    {K : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock K n)
    (f : Nat → Nat) (hf : StrictMono f)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf2 : f 2 = 2)
    (hf4 : f 4 < n)
    (hInduced : ∀ x y z : Nat,
      x < y → y < z → z < 5 →
      (K.edge (f x) (f y) (f z) ↔
        oldCutFiveVertexPrediary.edge x y z)) :
    ¬ (oldCutFiveVertexPrediary.SameOneTypeBelow 3 3 4 →
       K.SameOneTypeBelow (f 3) (f 3) (f 4)) := by
  have hge3 : 3 ≤ f 3 := by
    have h := hf (show (2 : Nat) < 3 by omega)
    rw [hf2] at h
    omega
  have hge4 : 3 ≤ f 4 := by
    have h := hf (show (2 : Nat) < 4 by omega)
    rw [hf2] at h
    omega
  have hLeaf3 : IsLeaf K (f 3) := by
    refine ⟨hge3, ?_, ?_⟩
    · intro he
      have hTarget : K.edge (f 0) (f 1) (f 3) := by
        simpa only [hf0, hf1] using he
      have hSource := (hInduced 0 1 3
        (by omega) (by omega) (by omega)).mp hTarget
      simpa [oldCutFiveVertexPrediary] using hSource
    · intro he
      have hTarget : K.edge (f 0) (f 2) (f 3) := by
        simpa only [hf0, hf2] using he
      have hSource := (hInduced 0 2 3
        (by omega) (by omega) (by omega)).mp hTarget
      simpa [oldCutFiveVertexPrediary] using hSource
  have hLeaf4 : IsLeaf K (f 4) := by
    refine ⟨hge4, ?_, ?_⟩
    · intro he
      have hTarget : K.edge (f 0) (f 1) (f 4) := by
        simpa only [hf0, hf1] using he
      have hSource := (hInduced 0 1 4
        (by omega) (by omega) (by omega)).mp hTarget
      simpa [oldCutFiveVertexPrediary] using hSource
    · intro he
      have hTarget : K.edge (f 0) (f 2) (f 4) := by
        simpa only [hf0, hf2] using he
      have hSource := (hInduced 0 2 4
        (by omega) (by omega) (by omega)).mp hTarget
      simpa [oldCutFiveVertexPrediary] using hSource
  exact oldCutFiveVertex_no_finite_preserving_completion
    D f hf hf4 hLeaf3 hLeaf4

end DiaryLeafPriority
end ThreeUniformDiaries
