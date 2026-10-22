import ThreeUniformDiaries.DiaryFiniteRoleBlockInterface
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex
import ThreeUniformDiaries.DiaryFiniteExplicitSmallTargetDiary
import ThreeUniformDiaries.DiaryFiniteFlipFirstDirection

/-!
# Full leaf-pair meets couple E2 orientations at distinct 1-splits

If two ordered pairs of diary leaves have full pair-type
meet past marker level 1, their marker-one auxiliary edge
incidences agree. By V3, each marker-one incidence records
the lexicographic right-branch orientation of its pair.
The E-only one-split formula identifies that orientation
with an E2 incidence at the pair's genuine singleton meet.

Consequently, preserved full pair-type meets impose
equalities between E2 columns at DIFFERENT one-splits.
These equalities survive ALL genuine flips of a diary.
Thus one-split flip controls do NOT form independent bits.

The concrete 9-vertex absorber illustrates the constraint:
pairs (6,8),(7,8) have full meet 3 and singleton meets 5,4,
so in EVERY target flip T the bits E_T(0,5,8) and
E_T(0,4,8) are identical. This is a substantive V3/S2
coupling relevant to the unfinished global target geometry.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Pair-type agreement through the Devlin marker-one cut
forces right E2 orientation bits to agree, possibly at two
DIFFERENT genuine singleton split vertices. -/
theorem finite_pairMeet_couples_oneSplit_right_bits
    {H : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock H n)
    (a b c d s t : Nat)
    (hab : a < b) (hcd : c < d)
    (hbn : b < n) (hdn : d < n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hs : IsOneSplit H s) (ht : IsOneSplit H t)
    (hsa : s < a) (htc : t < c)
    (hAB : H.oneMeetLevel a b = s)
    (hCD : H.oneMeetLevel c d = t)
    (hPairMeet : 1 < H.twoMeetLevel a b c d) :
    (H.edge 0 s b ↔ H.edge 0 t d) := by
  have hMarkers : H.edge 1 a b ↔ H.edge 1 c d :=
    (H.twoMeetLevel_agree a b c d).2.2 hPairMeet
  have hABMarker : H.edge 1 a b ↔ H.edge 0 s b :=
    (D.prediary.leaf_marker_one a b hab hbn ha hb).trans
      (E_oneSplit_lexEarlier_iff_right
        D.prediary.permitted_edge s a b hs hab hsa hAB)
  have hCDMarker : H.edge 1 c d ↔ H.edge 0 t d :=
    (D.prediary.leaf_marker_one c d hcd hdn hc hd).trans
      (E_oneSplit_lexEarlier_iff_right
        D.prediary.permitted_edge t c d ht hcd htc hCD)
  exact hABMarker.symm.trans (hMarkers.trans hCDMarker)

/-- In EVERY genuine flip of the explicit nine-vertex diary,
the two E2 orientations at 1-splits 5 and 4 are coupled
through the Devlin marker-one bits of pairs (6,8),(7,8). -/
theorem smallFlipTarget_every_flip_couples_E2_splits
    {T : Ordered3Graph Nat}
    (F : FiniteDiaryFlip smallFlipTarget T 9) :
    T.edge 0 5 8 ↔ T.edge 0 4 8 := by
  have h5 : IsOneSplit T 5 :=
    ((F.role_iff 5 smallFlipTarget_oneSplit5.1 (by omega)).2.1).mp
      smallFlipTarget_oneSplit5
  have h4 : IsOneSplit T 4 :=
    ((F.role_iff 4 smallFlipTarget_oneSplit4.1 (by omega)).2.1).mp
      smallFlipTarget_oneSplit4
  have h6 : IsLeaf T 6 :=
    ((F.role_iff 6 smallFlipTarget_leaf6.1 (by omega)).1).mp
      smallFlipTarget_leaf6
  have h7 : IsLeaf T 7 :=
    ((F.role_iff 7 smallFlipTarget_leaf7.1 (by omega)).1).mp
      smallFlipTarget_leaf7
  have h8 : IsLeaf T 8 :=
    ((F.role_iff 8 smallFlipTarget_leaf8.1 (by omega)).1).mp
      smallFlipTarget_leaf8
  have hMeet68 : T.oneMeetLevel 6 8 = 5 :=
    (F.leaf_oneMeet 6 8 (by omega) (by omega)
      smallFlipTarget_leaf6 smallFlipTarget_leaf8).symm.trans
        smallFlipTarget_meet_6_8
  have hMeet78 : T.oneMeetLevel 7 8 = 4 :=
    (F.leaf_oneMeet 7 8 (by omega) (by omega)
      smallFlipTarget_leaf7 smallFlipTarget_leaf8).symm.trans
        smallFlipTarget_meet_7_8
  have hPair : T.twoMeetLevel 6 8 7 8 = 3 :=
    (F.leaf_twoMeet 6 8 7 8
      (by omega) (by omega) (by omega) (by omega)
      smallFlipTarget_leaf6 smallFlipTarget_leaf8
      smallFlipTarget_leaf7 smallFlipTarget_leaf8).symm.trans
        smallFlipTarget_twoMeet_68_78
  exact finite_pairMeet_couples_oneSplit_right_bits
    F.target_diary
    6 8 7 8 5 4
    (by omega) (by omega) (by omega) (by omega)
    h6 h8 h7 h8 h5 h4
    (by omega) (by omega) hMeet68 hMeet78
    (by rw [hPair]; omega)

end DiaryLeafPriority
end ThreeUniformDiaries
