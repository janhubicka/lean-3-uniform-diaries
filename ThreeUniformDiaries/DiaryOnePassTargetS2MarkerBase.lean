import ThreeUniformDiaries.DiaryOnePassTargetPrediary
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# S2 marker case: pairs with opposite Devlin-1 bits meet at level 1

For ANY V/E pre-diary, edges (0,a,b) with a a leaf are forbidden by
the five permitted-edge forms. Thus two ordered pairs of leaves have
identical full two-types through cut 1: the singleton components are
vacuous, and their auxiliary coordinate zero is absent.

If the genuine marker-1 edges (1,a,b), (1,c,d) have opposite bits,
these are exactly the first differing auxiliary tests. Hence the
literal full twoMeetLevel is numerically ONE.

Applied to the actual one-pass target via its now verified pre-diary
structure, this proves the opposite-orientation part of S2 without
any S1/S2 assumptions. The same-marker case (meet at old/fresh
2-split or genuine terminal cap) is a separate remaining obligation.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- No (0,a,b) edge is permitted if a is a genuine leaf.
This is a pure (E) consequence, independent of diary meet axioms. -/
theorem RolePrediary.no_zero_leaf_pair_edge
    (P : RolePrediary H) (a b : Nat) (ha : IsLeaf H a) :
    ¬ H.edge 0 a b := by
  intro he
  rcases P.permitted_edge 0 a b he with
    hMarker | hOne | hTwo | hDevlin | hNormal
  · rcases hMarker.2.1 with h | h <;> omega
  · exact ha.2.1 hOne.2.1.2.1
  · have hbad := hTwo.1.1
    omega
  · rcases hDevlin.1 with h | h <;> omega
  · have hbad := hNormal.1.1
    omega

/-- The full two-types of ANY two genuine ordered leaf pairs
agree at the initial cut 1, using only permitted-edge shapes. -/
theorem RolePrediary.leaf_pairs_sameTwoTypeBelow_one
    (P : RolePrediary H) (a b c d : Nat)
    (ha : IsLeaf H a) (hc : IsLeaf H c) :
    H.SameTwoTypeBelow 1 a b c d := by
  constructor
  · intro x y hxy hy
    omega
  constructor
  · intro x y hxy hy
    omega
  · intro x hx
    have hZero : x = 0 := by omega
    subst x
    exact iff_of_false
      (P.no_zero_leaf_pair_edge a b ha)
      (P.no_zero_leaf_pair_edge c d hc)

/-- Exact S2 marker-1 case in an arbitrary pre-diary:
opposite marker-1 auxiliary bits force numerical pair meet 1. -/
theorem RolePrediary.twoMeet_eq_one_of_marker_disagreement
    (P : RolePrediary H) (a b c d : Nat)
    (ha : IsLeaf H a) (hc : IsLeaf H c)
    (hDifferent : ¬ (H.edge 1 a b ↔ H.edge 1 c d)) :
    H.twoMeetLevel a b c d = 1 := by
  classical
  have hCut : H.SameTwoTypeBelow 1 a b c d :=
    P.leaf_pairs_sameTwoTypeBelow_one a b c d ha hc
  have hBound : 1 ≤ min a c := by
    have ha3 := ha.1
    have hc3 := hc.1
    omega
  have hLower : 1 ≤ H.twoMeetLevel a b c d :=
    Nat.le_findGreatest hBound hCut
  have hUpper : H.twoMeetLevel a b c d < 2 := by
    by_contra hn
    have hGe : 2 ≤ H.twoMeetLevel a b c d := by omega
    have hAgree := H.twoMeetLevel_agree a b c d
    have hBit : H.edge 1 a b ↔ H.edge 1 c d :=
      hAgree.2.2 (by omega)
    exact hDifferent hBit
  omega

/-- The actual one-pass target satisfies S2 at all ordered
target leaf pairs having distinct marker-1 incidences. -/
theorem onePassRawTarget_twoMeet_eq_one_of_marker_disagreement
    (P : RolePrediary H) (a b c d : Nat)
    (ha : IsLeaf (onePassRawTarget H) a)
    (hc : IsLeaf (onePassRawTarget H) c)
    (hDifferent : ¬ ((onePassRawTarget H).edge 1 a b ↔
      (onePassRawTarget H).edge 1 c d)) :
    (onePassRawTarget H).twoMeetLevel a b c d = 1 :=
  (onePassRawTarget_isPrediary P).twoMeet_eq_one_of_marker_disagreement
    a b c d ha hc hDifferent

end DiaryLeafPriority
end ThreeUniformDiaries
