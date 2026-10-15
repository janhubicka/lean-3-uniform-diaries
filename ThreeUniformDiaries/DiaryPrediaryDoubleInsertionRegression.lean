import ThreeUniformDiaries.DiaryPrediaryDefinition
import ThreeUniformDiaries.DiaryPrediaryOneClassInsertion
import ThreeUniformDiaries.DiaryPrediaryTwoClassInsertion

/-!
# A concrete V3 obstruction after consecutive pre-diary insertions

Finite experiment: begin with four leaves 3,4,5,6, no
normal edges, and marker-1 edges on every ordered pair.
The first prescribed 1-split insertion at level 3 gives a
role-one vertex, and the next minimal defective full-pair
meet is again at 3. Applying the published 2-split insertion
to the old pair class represented by {4,5} yields the
nine-vertex picture encoded below.

The crucial final edges are:
  * (1,6,8), an ORIGINAL Devlin marker, and
  * (3,5,6), but NOT (3,5,8), introduced at the 2-split.

The latter causes oneMeet(6,8)=5 and the mixed pair
twoMeet(5,6;5,8)=3, hence LexEarlier(6,8) is FALSE.
The unchanged marker (1,6,8) is TRUE. Consequently
the final hypergraph violates V3.

This file proves that finite picture has the claimed
genuine one-/two-type meets and violates the literal V3
part of RolePrediary. The separate claim that it is the
output of the manuscript's specific TWO recursive
insertions is recorded as an English audit obligation
rather than being silently assumed in a Lean theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryPrediaryRegression

open Ordered3Graph
open DiaryLeafPriority

/-- The explicit second-stage nine-vertex edge picture.
Only increasing triples are declared to be hyperedges. -/
def badSecondStage : Ordered3Graph Nat where
  edge x y z :=
    (x = 0 ∧ y = 1 ∧ z = 4) ∨
    (x = 0 ∧ y = 2 ∧ z = 3) ∨
    (x = 0 ∧ y = 4 ∧ (z = 6 ∨ z = 7 ∨ z = 8)) ∨
    (x = 1 ∧ 5 ≤ y ∧ y < z ∧ z ≤ 8) ∨
    (x = 3 ∧ y = 5 ∧ (z = 6 ∨ z = 7))

/-- The leaf types of 6 and 8 agree through cut 5. -/
theorem pair_6_8_agree_below_5 :
    badSecondStage.SameOneTypeBelow 5 6 8 := by
  have hFinite :
      ∀ a b : Fin 5, a < b →
        (badSecondStage.edge a.val b.val 6 ↔
         badSecondStage.edge a.val b.val 8) := by
    decide
  intro a b hab hb
  have ha : a < 5 := by omega
  exact hFinite ⟨a,ha⟩ ⟨b,hb⟩ (by simpa using hab)

/-- The new (3,5,-) test separates the same leaf types
at the very next cut. -/
theorem pair_6_8_disagree_below_6 :
    ¬ badSecondStage.SameOneTypeBelow 6 6 8 := by
  intro h
  have heq := h (a := 3) (b := 5) (by omega) (by omega)
  norm_num [badSecondStage] at heq

theorem pair_6_8_oneMeet_eq_5 :
    badSecondStage.oneMeetLevel 6 8 = 5 := by
  classical
  have hlow : 5 ≤ badSecondStage.oneMeetLevel 6 8 := by
    apply Nat.le_findGreatest (by omega)
    exact pair_6_8_agree_below_5
  have hhigh : badSecondStage.oneMeetLevel 6 8 ≤ 5 := by
    by_contra hnot
    have hmeet := badSecondStage.oneMeetLevel_agree 6 8
    apply pair_6_8_disagree_below_6
    intro a b hab hb
    exact hmeet hab (by omega)
  omega

/-- The two pairs (5,6) and (5,8) agree as full
ordered 2-types through cut 3. -/
theorem pairs_56_58_agree_below_3 :
    badSecondStage.SameTwoTypeBelow 3 5 6 5 8 := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab hb
    rfl
  · intro a b hab hb
    exact pair_6_8_agree_below_5 hab (by omega)
  · have hFinite :
        ∀ a : Fin 3,
          (badSecondStage.edge a.val 5 6 ↔
           badSecondStage.edge a.val 5 8) := by
      decide
    intro a ha
    exact hFinite ⟨a,ha⟩

theorem pairs_56_58_disagree_below_4 :
    ¬ badSecondStage.SameTwoTypeBelow 4 5 6 5 8 := by
  intro h
  have heq := h.2.2 (a := 3) (by omega)
  norm_num [badSecondStage] at heq

theorem pairs_56_58_twoMeet_eq_3 :
    badSecondStage.twoMeetLevel 5 6 5 8 = 3 := by
  classical
  have hlow : 3 ≤ badSecondStage.twoMeetLevel 5 6 5 8 := by
    apply Nat.le_findGreatest (by omega)
    exact pairs_56_58_agree_below_3
  have hhigh : badSecondStage.twoMeetLevel 5 6 5 8 ≤ 3 := by
    by_contra hnot
    have hmeet := badSecondStage.twoMeetLevel_agree 5 6 5 8
    apply pairs_56_58_disagree_below_4
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab hb
      exact hmeet.1 hab (by omega)
    · intro a b hab hb
      exact hmeet.2.1 hab (by omega)
    · intro a ha
      exact hmeet.2.2 (by omega)
  omega

/-- The literal lex order has REVERSED on leaf pair (6,8),
despite the unchanged marker edge (1,6,8). -/
theorem not_lex_6_8 :
    ¬ LexEarlier badSecondStage 6 8 := by
  simp [LexEarlier, pair_6_8_oneMeet_eq_5,
    pairs_56_58_twoMeet_eq_3, badSecondStage]

theorem marker_one_6_8 :
    badSecondStage.edge 1 6 8 := by
  norm_num [badSecondStage]

theorem leaf_6 : IsLeaf badSecondStage 6 := by
  norm_num [IsLeaf, badSecondStage]

theorem leaf_8 : IsLeaf badSecondStage 8 := by
  norm_num [IsLeaf, badSecondStage]

/-- The explicit second stage FAILS V3. Consequently the
"it is easy to verify that H_{i+1} remains a pre-diary"
sentence cannot be used without a new insertion invariant
or a different construction. -/
theorem secondStage_not_prediary :
    ¬ RolePrediary badSecondStage := by
  intro P
  have hMarker := (P.leaf_marker_one 6 8 (by omega) leaf_6 leaf_8).mp
    marker_one_6_8
  exact not_lex_6_8 hMarker

end DiaryPrediaryRegression
end ThreeUniformDiaries
