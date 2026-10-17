import ThreeUniformDiaries.DiaryOnePassTargetS2MarkerBase
import ThreeUniformDiaries.DiaryOnePassSourceLeafMarkerBase

/-!
# S2 marker dichotomy: full pair-type meets are either 1 or >= 3

Every V/E pre-diary gives two complementary Devlin marker bits on
each genuine ordered leaf pair (a,b). If two pairs have different
marker-1 bits, the previously proved literal full 2-meet equals 1.

If they have the SAME marker-1 bit, both Devlin marker tests (at
coordinates 1 and 2) agree. Their two singleton coordinates agree
below the cut 3 (all earlier middle-coordinate tests are forbidden
for leaves), and the auxiliary coordinate 0 is absent. Thus their
FULL two-types agree below 3, and their literal twoMeetLevel is
at least 3.

This statement needs neither source S1/S2 nor completion and isolates
the exact hard remaining S2 case at/after an original/fresh event.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- If both ordered genuine leaf pairs have the same marker-one
incidence, their FULL two-types agree below marker cut three. -/
theorem RolePrediary.sameMarkerOne_twoTypeBelow_three
    (P : RolePrediary H)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hOne : (H.edge 1 a b ↔ H.edge 1 c d)) :
    H.SameTwoTypeBelow 3 a b c d := by
  have hLex : LexEarlier H a b ↔ LexEarlier H c d :=
    (P.leaf_marker_one a b hab ha hb).symm.trans
      (hOne.trans (P.leaf_marker_one c d hcd hc hd))
  have hMarkerTwo : (H.edge 2 a b ↔ H.edge 2 c d) :=
    (P.leaf_marker_two a b hab ha hb).trans
      ((not_congr hLex).trans
        (P.leaf_marker_two c d hcd hc hd).symm)
  refine ⟨onePass_source_leaves_sameOneTypeBelow_three P a c ha hc,
    onePass_source_leaves_sameOneTypeBelow_three P b d hb hd, ?_⟩
  intro x hx
  by_cases h0 : x = 0
  · subst x
    exact iff_of_false
      (P.no_zero_leaf_pair_edge a b ha)
      (P.no_zero_leaf_pair_edge c d hc)
  by_cases h1 : x = 1
  · subst x
    exact hOne
  have h2 : x = 2 := by omega
  subst x
  exact hMarkerTwo

/-- S2's marker-stage dichotomy in ANY genuine V/E pre-diary.
Every pair of ordered leaf pairs meets either exactly at one or
at a level at least three, never at zero or two. -/
theorem RolePrediary.twoMeet_eq_one_or_ge_three
    (P : RolePrediary H)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d) :
    H.twoMeetLevel a b c d = 1 ∨
      3 ≤ H.twoMeetLevel a b c d := by
  classical
  by_cases hMarker : (H.edge 1 a b ↔ H.edge 1 c d)
  · right
    have hBelow := P.sameMarkerOne_twoTypeBelow_three
      a b c d hab hcd ha hb hc hd hMarker
    have hBound : 3 ≤ min a c := by
      have ha3 := ha.1
      have hc3 := hc.1
      omega
    exact Nat.le_findGreatest hBound hBelow
  · left
    exact P.twoMeet_eq_one_of_marker_disagreement
      a b c d ha hc hMarker

/-- The exact same disjunction for the concrete one-pass
pre-diary target, with all target leaves represented genuinely. -/
theorem onePassRawTarget_twoMeet_eq_one_or_ge_three
    (P : RolePrediary H)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf (onePassRawTarget H) a)
    (hb : IsLeaf (onePassRawTarget H) b)
    (hc : IsLeaf (onePassRawTarget H) c)
    (hd : IsLeaf (onePassRawTarget H) d) :
    (onePassRawTarget H).twoMeetLevel a b c d = 1 ∨
      3 ≤ (onePassRawTarget H).twoMeetLevel a b c d :=
  (onePassRawTarget_isPrediary P).twoMeet_eq_one_or_ge_three
    a b c d hab hcd ha hb hc hd

end DiaryLeafPriority
end ThreeUniformDiaries
