import ThreeUniformDiaries.DiaryProtectedMixedNumericalMeets

/-!
# Exact singleton meets when a source endpoint is a split

The one-pass global singleton transport lemma was proved for pairs of
source leaves, which does not directly apply to protected mixed pairs.
A split vertex, however, has no incoming singleton test after the
three marker levels by (E), and the one-pass old map fixes exactly
those initial marker levels.

For a pair with at least one split:
* if the marker singleton types disagree, the original and target
  one-meets are both below 3 and agree exactly;
* if they agree, the other vertex has the same split role, so the
  singleton types agree through the cap in source and target.
Consequently the actual one-pass embedding preserves the numerical
singleton meet of every such pair, without source S1/S2.

No full protected mixed two-meet or flip-absorption theorem follows
without handling leaf-versus-leaf coordinate meets as well.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- At ANY marker cut up to three, the one-pass old image preserves
and reflects exact singleton-type agreement, for arbitrary original
vertices, not only leaves or splits. -/
theorem onePass_oneTypeBelow_markerCut_iff
    (H : Ordered3Graph Nat) (k u v : Nat) (hk : k ≤ 3) :
    H.SameOneTypeBelow k u v ↔
      (onePassRawTarget H).SameOneTypeBelow k
        (onePassOldImage H u) (onePassOldImage H v) := by
  constructor
  · intro hs a b hab hb
    have ha3 : a < 3 := by omega
    have hb3 : b < 3 := by omega
    have hu := onePassRawTarget_edge_image_iff H a b u
    have hv := onePassRawTarget_edge_image_iff H a b v
    rw [onePassOldImage_fixed_below_three H a ha3,
      onePassOldImage_fixed_below_three H b hb3] at hu hv
    exact hu.trans ((hs hab hb).trans hv.symm)
  · intro ht a b hab hb
    have ha3 : a < 3 := by omega
    have hb3 : b < 3 := by omega
    have hu := onePassRawTarget_edge_image_iff H a b u
    have hv := onePassRawTarget_edge_image_iff H a b v
    rw [onePassOldImage_fixed_below_three H a ha3,
      onePassOldImage_fixed_below_three H b hb3] at hu hv
    exact hu.symm.trans ((ht hab hb).trans hv)

/-- If the three-marker singleton type of a split agrees with that
of another vertex at or above 3, the latter has exactly the same
one-split or two-split role. -/
theorem isDiarySplit_of_same_marker_type
    (H : Ordered3Graph Nat) (u v : Nat)
    (hu : IsDiarySplit H u) (hv : 3 ≤ v)
    (hSame : H.SameOneTypeBelow 3 u v) :
    IsDiarySplit H v := by
  have h01 : H.edge 0 1 u ↔ H.edge 0 1 v :=
    hSame (show 0 < (1 : Nat) by omega) (show (1 : Nat) < 3 by omega)
  have h02 : H.edge 0 2 u ↔ H.edge 0 2 v :=
    hSame (show 0 < (2 : Nat) by omega) (show (2 : Nat) < 3 by omega)
  rcases hu with hOne | hTwo
  · left
    refine ⟨hv, h01.mp hOne.2.1, ?_⟩
    intro hv2
    exact hOne.2.2 (h02.mpr hv2)
  · right
    refine ⟨hv, ?_, h02.mp hTwo.2.2⟩
    intro hv1
    exact hTwo.2.1 (h01.mpr hv1)

/-- If the original singleton types already disagree by marker
cut 3, their numerical one-meets are below 3. The old embedding
fixes this level and preserves the complete agreement sequence
there, hence it preserves the exact meet. -/
theorem onePass_oneMeet_preserved_of_marker_disagreement
    (H : Ordered3Graph Nat) (u v : Nat)
    (hu : 3 ≤ u) (hv : 3 ≤ v)
    (hDiff : ¬ H.SameOneTypeBelow 3 u v) :
    (onePassRawTarget H).oneMeetLevel
        (onePassOldImage H u) (onePassOldImage H v) =
      onePassOldImage H (H.oneMeetLevel u v) := by
  classical
  let G := onePassRawTarget H
  let f := onePassOldImage H
  let w := H.oneMeetLevel u v
  let z := G.oneMeetLevel (f u) (f v)
  have hw3 : w < 3 := by
    by_contra hn
    have hge : 3 ≤ w := by omega
    apply hDiff
    intro a b hab hb
    exact (H.oneMeetLevel_agree u v) hab (by omega)
  have hTargetDiff : ¬ G.SameOneTypeBelow 3 (f u) (f v) := by
    intro h
    exact hDiff ((onePass_oneTypeBelow_three_iff H u v).mpr h)
  have hz3 : z < 3 := by
    by_contra hn
    have hge : 3 ≤ z := by omega
    apply hTargetDiff
    intro a b hab hb
    exact (G.oneMeetLevel_agree (f u) (f v)) hab (by omega)
  have hfu : 3 ≤ f u :=
    (onePassOldImage_ge_three_iff H u).mpr hu
  have hfv : 3 ≤ f v :=
    (onePassOldImage_ge_three_iff H v).mpr hv
  have hAtW : G.SameOneTypeBelow w (f u) (f v) :=
    (onePass_oneTypeBelow_markerCut_iff H w u v (by omega)).mp
      (H.oneMeetLevel_agree u v)
  have hAtZ : H.SameOneTypeBelow z u v :=
    (onePass_oneTypeBelow_markerCut_iff H z u v (by omega)).mpr
      (G.oneMeetLevel_agree (f u) (f v))
  have hwle : w ≤ z :=
    Nat.le_findGreatest (by omega : w ≤ min (f u) (f v)) hAtW
  have hzle : z ≤ w :=
    Nat.le_findGreatest (by omega : z ≤ min u v) hAtZ
  have heq : z = w := by omega
  calc
    G.oneMeetLevel (f u) (f v) = w := heq
    _ = f w := (onePassOldImage_fixed_below_three H w hw3).symm
    _ = f (H.oneMeetLevel u v) := rfl

/-- One-pass completion preserves the literal numerical singleton
meet when at least one member is a genuine one-split/two-split
vertex. This handles both equal marker profiles (capped meets)
and unequal profiles (meets below 3), using source V/E only. -/
theorem onePass_oneMeet_preserved_of_split
    (P : RolePrediary H) (u v : Nat)
    (hu : 3 ≤ u) (hv : 3 ≤ v)
    (hSplit : IsDiarySplit H u ∨ IsDiarySplit H v) :
    (onePassRawTarget H).oneMeetLevel
        (onePassOldImage H u) (onePassOldImage H v) =
      onePassOldImage H (H.oneMeetLevel u v) := by
  classical
  let G := onePassRawTarget H
  let f := onePassOldImage H
  by_cases hSame : H.SameOneTypeBelow 3 u v
  · have hBoth : IsDiarySplit H u ∧ IsDiarySplit H v := by
      rcases hSplit with hU | hV
      · exact ⟨hU, isDiarySplit_of_same_marker_type H u v hU hv hSame⟩
      · have hReverse : H.SameOneTypeBelow 3 v u := by
          intro a b hab hb
          exact (hSame hab hb).symm
        exact ⟨isDiarySplit_of_same_marker_type H v u hV hu hReverse, hV⟩
    have hSourceCap3 : 3 ≤ min u v := by omega
    have hSourceAtCap : H.SameOneTypeBelow (min u v) u v :=
      (P.split_oneType_stable_after_three
        (min u v) u v hSourceCap3 hBoth.1 hBoth.2).mpr hSame
    have hSourceMeet : H.oneMeetLevel u v = min u v := by
      apply le_antisymm (H.oneMeetLevel_le_min u v)
      exact Nat.le_findGreatest (le_refl _) hSourceAtCap
    have hBothTarget :
        IsDiarySplit G (f u) ∧ IsDiarySplit G (f v) :=
      ⟨(onePassOldImage_isDiarySplit H u).mp hBoth.1,
       (onePassOldImage_isDiarySplit H v).mp hBoth.2⟩
    have hTargetMarker : G.SameOneTypeBelow 3 (f u) (f v) :=
      (onePass_oneTypeBelow_three_iff H u v).mp hSame
    have hTargetCap3 : 3 ≤ min (f u) (f v) := by
      have hfu : 3 ≤ f u := (onePassOldImage_ge_three_iff H u).mpr hu
      have hfv : 3 ≤ f v := (onePassOldImage_ge_three_iff H v).mpr hv
      omega
    have hTargetAtCap : G.SameOneTypeBelow (min (f u) (f v))
        (f u) (f v) :=
      ((onePassRawTarget_isPrediary P).split_oneType_stable_after_three
        (min (f u) (f v)) (f u) (f v)
        hTargetCap3 hBothTarget.1 hBothTarget.2).mpr hTargetMarker
    have hTargetMeet : G.oneMeetLevel (f u) (f v) = min (f u) (f v) := by
      apply le_antisymm (G.oneMeetLevel_le_min (f u) (f v))
      exact Nat.le_findGreatest (le_refl _) hTargetAtCap
    rw [hTargetMeet, hSourceMeet]
    exact (onePassOldImage_min H u v).symm
  · exact onePass_oneMeet_preserved_of_marker_disagreement H u v hu hv hSame

end DiaryLeafPriority
end ThreeUniformDiaries
