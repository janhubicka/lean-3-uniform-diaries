import ThreeUniformDiaries.DiaryPrediaryDefinition
import ThreeUniformDiaries.ExactTypeMeetLevels

/-!
# Marker cut three is a common singleton prefix of ALL genuine leaves

The V/E source pre-diary's permitted edge shapes imply that every
increasing test (a,b,u) with b<3 and u an actual source leaf is
negative. This includes (1,2,u), not only the two direct role marker
tests (0,1,u) and (0,2,u).

Hence every two leaves have the same singleton type below cut 3,
and their numerical singleton meet is at least 3. This uses NO
source S1/S2 and is needed for the global one-pass V3 case split
at the actual first singleton meet.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Every singleton test using only distinguished marker coordinates
is negative when the tested endpoint is a genuine source leaf. -/
theorem onePass_source_leaf_no_middle_below_three
    (P : RolePrediary H) (u a b : Nat)
    (hu : IsLeaf H u)
    (hab : a < b) (hb3 : b < 3) :
    ¬ H.edge a b u := by
  intro he
  rcases P.permitted_edge a b u he with
    hMarker | hOne | hTwo | hDevlin | hNormal
  · obtain ⟨ha,hb,_⟩ := hMarker
    subst a
    rcases hb with hb | hb
    · subst b
      exact hu.2.1 he
    · subst b
      exact hu.2.2 he
  · have hb : 3 ≤ b := hOne.2.1.1
    omega
  · have ha : 3 ≤ a := hTwo.1.1
    omega
  · have hb : 3 ≤ b := hDevlin.2.1.1
    omega
  · have ha : 3 ≤ a := hNormal.1.1
    omega

/-- The actual 1-types of every two source leaves agree below
the unchanged three Devlin/role-marker coordinates. -/
theorem onePass_source_leaves_sameOneTypeBelow_three
    (P : RolePrediary H) (u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v) :
    H.SameOneTypeBelow 3 u v := by
  intro a b hab hb
  exact iff_of_false
    (onePass_source_leaf_no_middle_below_three P u a b hu hab hb)
    (onePass_source_leaf_no_middle_below_three P v a b hv hab hb)

/-- The actual first singleton meet of any two source leaves
cannot precede marker cut three. -/
theorem onePass_source_leaf_oneMeet_ge_three
    (P : RolePrediary H) (u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v) :
    3 ≤ H.oneMeetLevel u v := by
  classical
  have hBound : 3 ≤ min u v := by
    have hu3 := hu.1
    have hv3 := hv.1
    omega
  exact Nat.le_findGreatest hBound
    (onePass_source_leaves_sameOneTypeBelow_three P u v hu hv)

end DiaryLeafPriority
end ThreeUniformDiaries
