import ThreeUniformDiaries.DiaryTwoLeafSupportNoTwoSplit
import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# One binary orientation controls the mixed edge profile of two leaves

At the SECOND selected source leaf, the generated support contains
the three markers, two distinct leaves, and their singleton meet.
The previously verified no-two-split theorem removes E3 events.

For one ordered pair of leaves a<b, write s = a meet b. The
four potentially variable E2/V3 incidences are

    E(0,s,a), E(0,s,b), E(1,a,b), E(2,a,b).

The diary's V-clauses and the exact split/leaf marker identities
make all four bits functions of a SINGLE choice: E(0,s,b).
Consequently matching the right split/leaf bit of the source and
target forces agreement of the entire four-bit profile.

This is independent of target leaf genericity and does not assert
that a new target leaf satisfying the required bit exists. In
particular it cannot by itself extend a fixed first-leaf image.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- S1 and the role of a true target leaf force the singleton
meet with a distinct leaf to lie STRICTLY before the left leaf.
The usual upper bound alone only gives a non-strict inequality. -/
theorem RoleDiary.oneMeet_lt_left_of_distinct_leaves
    {H : Ordered3Graph Nat}
    (D : RoleDiary H) (a b : Nat)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hab : a ≠ b) :
    H.oneMeetLevel a b < a := by
  have hSplit : IsOneSplit H (H.oneMeetLevel a b) :=
    D.singleton_meets a b ha hb hab
  have hBound : H.oneMeetLevel a b ≤ a :=
    (H.oneMeetLevel_le_min a b).trans (min_le_left _ _)
  have hNotEq : H.oneMeetLevel a b ≠ a := by
    intro heq
    have hOne : IsOneSplit H a := by
      simpa only [heq] using hSplit
    exact ha.2.1 hOne.2.1
  omega

/-- Compare the complete four-bit marker/singleton-split profile
of ordered source and target leaf pairs using ONE orientation bit.

The two input pairs need not belong to the same diary. Their one-meet
levels need not coincide numerically and are not assumed to be
separately embedded. The only hypothesis coupling the pairs is the
literal right split/leaf incidence equivalence. -/
theorem two_leaf_right_orientation_controls_marker_profile
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf K c) (hd : IsLeaf K d)
    (hRight :
      (H.edge 0 (H.oneMeetLevel a b) b ↔
       K.edge 0 (K.oneMeetLevel c d) d)) :
    (H.edge 0 (H.oneMeetLevel a b) a ↔
      K.edge 0 (K.oneMeetLevel c d) c) ∧
    (H.edge 1 a b ↔ K.edge 1 c d) ∧
    (H.edge 2 a b ↔ K.edge 2 c d) := by
  let s := H.oneMeetLevel a b
  let t := K.oneMeetLevel c d
  have hs : IsOneSplit H s :=
    DH.singleton_meets a b ha hb (ne_of_lt hab)
  have ht : IsOneSplit K t :=
    DK.singleton_meets c d hc hd (ne_of_lt hcd)
  have hsa : s < a :=
    DH.oneMeet_lt_left_of_distinct_leaves a b ha hb (ne_of_lt hab)
  have htc : t < c :=
    DK.oneMeet_lt_left_of_distinct_leaves c d hc hd (ne_of_lt hcd)
  obtain ⟨hSourceLeft,hSourceRight⟩ :=
    DH.oneSplit_left_right_marker s a b hs ha hb hab hsa rfl
  obtain ⟨hTargetLeft,hTargetRight⟩ :=
    DK.oneSplit_left_right_marker t c d ht hc hd hcd htc rfl
  have hM1 : H.edge 1 a b ↔ K.edge 1 c d :=
    hSourceRight.symm.trans (hRight.trans hTargetRight)
  have hLex : LexEarlier H a b ↔ LexEarlier K c d :=
    (DH.leaf_marker_one a b hab ha hb).symm.trans
      (hM1.trans (DK.leaf_marker_one c d hcd hc hd))
  have hM2 : H.edge 2 a b ↔ K.edge 2 c d :=
    (DH.leaf_marker_two a b hab ha hb).trans
      ((not_congr hLex).trans
        (DK.leaf_marker_two c d hcd hc hd).symm)
  have hLeft : H.edge 0 s a ↔ K.edge 0 t c :=
    hSourceLeft.trans (hM2.trans hTargetLeft.symm)
  exact ⟨hLeft,hM1,hM2⟩

/-- The four marker/mixed incidence tests for two ordered leaf
pairs are equivalent to the single right split/leaf incidence bit.
The reverse direction is immediate because that bit is explicitly
one of the four tests. -/
theorem two_leaf_complete_marker_profile_iff_right_orientation
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf K c) (hd : IsLeaf K d) :
    ((H.edge 0 (H.oneMeetLevel a b) a ↔
       K.edge 0 (K.oneMeetLevel c d) c) ∧
     (H.edge 0 (H.oneMeetLevel a b) b ↔
       K.edge 0 (K.oneMeetLevel c d) d) ∧
     (H.edge 1 a b ↔ K.edge 1 c d) ∧
     (H.edge 2 a b ↔ K.edge 2 c d)) ↔
    (H.edge 0 (H.oneMeetLevel a b) b ↔
      K.edge 0 (K.oneMeetLevel c d) d) := by
  constructor
  · intro h
    exact h.2.1
  · intro hRight
    obtain ⟨hLeft,hM1,hM2⟩ :=
      two_leaf_right_orientation_controls_marker_profile
        DH DK a b c d hab hcd ha hb hc hd hRight
    exact ⟨hLeft,hRight,hM1,hM2⟩

end DiaryLeafPriority
end ThreeUniformDiaries
