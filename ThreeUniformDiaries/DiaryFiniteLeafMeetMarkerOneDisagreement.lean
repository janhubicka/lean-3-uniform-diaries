import ThreeUniformDiaries.DiaryFiniteLeafMeetPrefixCompression
import ThreeUniformDiaries.DiaryFiniteLeafMeetMarkerReindex

/-!
# Exact compressed pair meets at the distinguished marker one

For genuine leaves, no singleton incidence can have middle
coordinate 1: strict edge order forces first coordinate zero,
and the leaf marker role prohibits edge(0,1,leaf).
Consequently a full ordered-pair meet equal to marker 1 must
be distinguished by the two pair-marker edges (1,a,b) and
(1,c,d).

The induced finite support retains markers 0,1,2 exactly. Thus
the distinguishing pair-marker incidence survives compression.
Forward two-type prefix transport yields lower bound 1; this
retained edge yields upper bound 1. No additional split vertices,
convexity or entire original type-coordinate set is needed.

This closes the marker-one case of the three S2 alternatives.
The proper 2-split and capped cases are separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {S : Finset Nat}

/-- No ordered ternary edge ends at a genuine leaf with middle
coordinate 1: the only possible first coordinate is 0, and
the leaf role forbids that marker edge. -/
theorem leaf_no_middle_one_edge
    (D : RoleDiary G)
    (a u : Nat) (hu : IsLeaf G u) :
    ¬ G.edge a 1 u := by
  intro he
  have hOrder := D.edge_ordered a 1 u he
  have h0 : a = 0 := by omega
  subst a
  exact hu.2.1 he

/-- If two pairs of genuine leaves first have different full
two-types at marker 1, their auxiliary marker-one bits differ.
Neither singleton column can contribute a test at middle 1. -/
theorem leaf_pair_twoMeet_one_marker_disagreement
    (D : RoleDiary G)
    (a b c d : Nat)
    (ha : IsLeaf G a) (hb : IsLeaf G b)
    (hc : IsLeaf G c) (hd : IsLeaf G d)
    (hMeet : G.twoMeetLevel a b c d = 1) :
    ¬ (G.edge 1 a b ↔ G.edge 1 c d) := by
  classical
  have hSourceAt : G.SameTwoTypeBelow 1 a b c d := by
    rw [← hMeet]
    exact G.twoMeetLevel_agree a b c d
  have hNotNext : ¬ G.SameTwoTypeBelow 2 a b c d := by
    intro hNext
    have hCap : 2 ≤ min a c := by
      have ha3 := ha.1
      have hc3 := hc.1
      omega
    have hTooLarge : 2 ≤ G.twoMeetLevel a b c d :=
      Nat.le_findGreatest hCap hNext
    omega
  intro hSame
  apply hNotNext
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hy
    by_cases hym : y < 1
    · exact hSourceAt.1 hxy hym
    · have hyeq : y = 1 := by omega
      subst y
      exact iff_of_false
        (leaf_no_middle_one_edge D x a ha)
        (leaf_no_middle_one_edge D x c hc)
  · intro x y hxy hy
    by_cases hym : y < 1
    · exact hSourceAt.2.1 hxy hym
    · have hyeq : y = 1 := by omega
      subst y
      exact iff_of_false
        (leaf_no_middle_one_edge D x b hb)
        (leaf_no_middle_one_edge D x d hd)
  · intro x hx
    by_cases hx0 : x < 1
    · exact hSourceAt.2.2 hx0
    · have hxeq : x = 1 := by omega
      subst x
      exact hSame

/-- A genuinely ordered selected leaf-pair comparison meeting
at original marker 1 still meets at indexed marker 1 after
induced finite compression (the first three indices are 0,1,2).
The source pair marker edges provide the upper bound. -/
theorem finiteSupportGraph_twoMeet_exact_at_marker_one
    (D : RoleDiary G)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (i j p q : Nat)
    (hi : i < S.card) (hj : j < S.card)
    (hp : p < S.card) (hq : q < S.card)
    (hij : i < j) (hpq : p < q)
    (hi3 : 3 ≤ i) (hp3 : 3 ≤ p)
    (ha : IsLeaf G (finiteSupportIndex S i))
    (hb : IsLeaf G (finiteSupportIndex S j))
    (hc : IsLeaf G (finiteSupportIndex S p))
    (hd : IsLeaf G (finiteSupportIndex S q))
    (hMeet : G.twoMeetLevel
       (finiteSupportIndex S i) (finiteSupportIndex S j)
       (finiteSupportIndex S p) (finiteSupportIndex S q) = 1) :
    (finiteSupportGraph G S).twoMeetLevel i j p q = 1 := by
  classical
  let H := finiteSupportGraph G S
  obtain ⟨hCard,hZero,hOne,_hTwo⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  have hDiff :
      ¬ (G.edge 1 (finiteSupportIndex S i) (finiteSupportIndex S j) ↔
         G.edge 1 (finiteSupportIndex S p) (finiteSupportIndex S q)) :=
    leaf_pair_twoMeet_one_marker_disagreement D
      (finiteSupportIndex S i) (finiteSupportIndex S j)
      (finiteSupportIndex S p) (finiteSupportIndex S q)
      ha hb hc hd hMeet
  have hSourceAt : G.SameTwoTypeBelow (finiteSupportIndex S 1)
      (finiteSupportIndex S i) (finiteSupportIndex S j)
      (finiteSupportIndex S p) (finiteSupportIndex S q) := by
    rw [hOne, ← hMeet]
    exact G.twoMeetLevel_agree
      (finiteSupportIndex S i) (finiteSupportIndex S j)
      (finiteSupportIndex S p) (finiteSupportIndex S q)
  have hTargetAt : H.SameTwoTypeBelow 1 i j p q :=
    finiteSupportGraph_twoType_of_original
      (G := G) (S := S) 1 i j p q
      (by omega) hi hj hp hq hij hpq (by omega) (by omega) hSourceAt
  have hLower : 1 ≤ H.twoMeetLevel i j p q :=
    Nat.le_findGreatest (by omega) hTargetAt
  have hTargetDiff : ¬ (H.edge 1 i j ↔ H.edge 1 p q) := by
    intro heq
    have hab := finiteSupportGraph_edge_iff G S 1 i j
      (by omega) hij hj
    have hcd := finiteSupportGraph_edge_iff G S 1 p q
      (by omega) hpq hq
    rw [hOne] at hab hcd
    exact hDiff (hab.symm.trans (heq.trans hcd))
  have hUpper : H.twoMeetLevel i j p q ≤ 1 := by
    by_contra hn
    have hGreater : 1 < H.twoMeetLevel i j p q := by omega
    have hAgree := H.twoMeetLevel_agree i j p q
    exact hTargetDiff (hAgree.2.2 hGreater)
  change H.twoMeetLevel i j p q = 1
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
