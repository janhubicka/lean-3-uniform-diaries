import ThreeUniformDiaries.DiaryProtectedSplitSingletonMeets
import ThreeUniformDiaries.DiaryOnePassTargetS2MarkerDichotomy
import ThreeUniformDiaries.DiaryProtectedMixedNumericalMeets

/-!
# Cross-role pair comparisons meet before marker cut three

A protected copy has full pair-type comparisons in which one
ordered pair contains a split and the other is an ordered pair
of leaves. Neither the all-leaf proof nor the both-mixed
auxiliary proof applies directly.

The two Devlin marker edges of every ordered LEAF pair are
complementary (V3), whereas both positive auxiliary marker
edges are forbidden for a split-containing pair (E). Therefore
the two pairs disagree before marker cut three, regardless of
the remaining hyperedges or future one-pass events.

The one-pass old image fixes all vertices below three and
copies their original edges exactly. This gives literal
numerical two-meet preservation for every cross-role
comparison of pairs whose first vertices are at least three.
No S1/S2 assumptions on the input are used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- All auxiliary type comparisons at an initial marker cut
k <= 3 are reflected exactly by the induced old copy. -/
theorem onePass_auxTypeBelow_markerCut_iff
    (H : Ordered3Graph Nat) (k a b c d : Nat) (hk : k ≤ 3) :
    H.SameAuxTypeBelow k a b c d ↔
      (onePassRawTarget H).SameAuxTypeBelow k
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  constructor
  · intro hs x hx
    have hx3 : x < 3 := by omega
    have hab := onePassRawTarget_edge_image_iff H x a b
    have hcd := onePassRawTarget_edge_image_iff H x c d
    rw [onePassOldImage_fixed_below_three H x hx3] at hab hcd
    exact hab.trans ((hs hx).trans hcd.symm)
  · intro ht x hx
    have hx3 : x < 3 := by omega
    have hab := onePassRawTarget_edge_image_iff H x a b
    have hcd := onePassRawTarget_edge_image_iff H x c d
    rw [onePassOldImage_fixed_below_three H x hx3] at hab hcd
    exact hab.symm.trans ((ht hx).trans hcd)

/-- Complete full two-type equivalence at EVERY initial marker
cut, even when the four original vertices have different roles.
In particular it does not rely on the global leaf-only transport
induction, which starts at original cut three. -/
theorem onePass_twoTypeBelow_markerCut_iff
    (H : Ordered3Graph Nat) (k a b c d : Nat) (hk : k ≤ 3) :
    H.SameTwoTypeBelow k a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow k
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  exact and_congr
    (onePass_oneTypeBelow_markerCut_iff H k a c hk)
    (and_congr
      (onePass_oneTypeBelow_markerCut_iff H k b d hk)
      (onePass_auxTypeBelow_markerCut_iff H k a b c d hk))

/-- Every genuine ordered pair of leaves has at least one
positive Devlin marker edge at positions one and two. -/
theorem RolePrediary.leaf_pair_has_positive_devlin_marker
    (P : RolePrediary H) (a b : Nat)
    (hab : a < b) (ha : IsLeaf H a) (hb : IsLeaf H b) :
    H.edge 1 a b ∨ H.edge 2 a b := by
  classical
  by_cases h : LexEarlier H a b
  · exact Or.inl ((P.leaf_marker_one a b hab ha hb).mpr h)
  · exact Or.inr ((P.leaf_marker_two a b hab ha hb).mpr h)

/-- A split-containing ordered pair and an all-leaf ordered pair
cannot agree in full two-type through cut three, in either order.
The obstruction is witnessed by a Devlin marker auxiliary bit. -/
theorem RolePrediary.cross_role_not_sameTwoTypeBelow_three
    (P : RolePrediary H) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (hCases :
      ((IsDiarySplit H a ∨ IsDiarySplit H b) ∧
        IsLeaf H c ∧ IsLeaf H d) ∨
      (IsLeaf H a ∧ IsLeaf H b ∧
        (IsDiarySplit H c ∨ IsDiarySplit H d))) :
    ¬ H.SameTwoTypeBelow 3 a b c d := by
  intro hSame
  rcases hCases with ⟨hMix, hc, hd⟩ | ⟨ha, hb, hMix⟩
  · have hNoOne : ¬ H.edge 1 a b :=
      P.mixed_pair_no_positive_aux_edge 1 a b (by omega) hMix
    have hNoTwo : ¬ H.edge 2 a b :=
      P.mixed_pair_no_positive_aux_edge 2 a b (by omega) hMix
    rcases P.leaf_pair_has_positive_devlin_marker c d hcd hc hd with
        hOne | hTwo
    · exact hNoOne ((hSame.2.2 (by omega : (1 : Nat) < 3)).mpr hOne)
    · exact hNoTwo ((hSame.2.2 (by omega : (2 : Nat) < 3)).mpr hTwo)
  · have hNoOne : ¬ H.edge 1 c d :=
      P.mixed_pair_no_positive_aux_edge 1 c d (by omega) hMix
    have hNoTwo : ¬ H.edge 2 c d :=
      P.mixed_pair_no_positive_aux_edge 2 c d (by omega) hMix
    rcases P.leaf_pair_has_positive_devlin_marker a b hab ha hb with
        hOne | hTwo
    · exact hNoOne ((hSame.2.2 (by omega : (1 : Nat) < 3)).mp hOne)
    · exact hNoTwo ((hSame.2.2 (by omega : (2 : Nat) < 3)).mp hTwo)

/-- Numerical full two-type meets of any split-containing pair
against any all-leaf pair are strictly below marker cut three,
as long as both first vertices are >= 3 and the pairs are
ordered. The same is true in either pair orientation. -/
theorem RolePrediary.cross_role_twoMeet_lt_three
    (P : RolePrediary H) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (hc3 : 3 ≤ c)
    (hCases :
      ((IsDiarySplit H a ∨ IsDiarySplit H b) ∧
        IsLeaf H c ∧ IsLeaf H d) ∨
      (IsLeaf H a ∧ IsLeaf H b ∧
        (IsDiarySplit H c ∨ IsDiarySplit H d))) :
    H.twoMeetLevel a b c d < 3 := by
  by_contra hNot
  have hGe : 3 ≤ H.twoMeetLevel a b c d := by omega
  have hFull := H.twoMeetLevel_agree a b c d
  have hAtThree : H.SameTwoTypeBelow 3 a b c d := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      exact hFull.1 hxy (by omega)
    · intro x y hxy hy
      exact hFull.2.1 hxy (by omega)
    · intro x hx
      exact hFull.2.2 (by omega)
  exact P.cross_role_not_sameTwoTypeBelow_three
    a b c d hab hcd hCases hAtThree

/-- EXACT one-pass numerical full two-meet preservation in the
previously untreated cross-role case. This is unconditional on the
source V/E pre-diary, and does not require protected S1/S2:
the meet is already below three, where the old embedding is
literally the identity. -/
theorem onePass_crossRole_twoMeet_preserved
    (P : RolePrediary H) (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (hc3 : 3 ≤ c)
    (hCases :
      ((IsDiarySplit H a ∨ IsDiarySplit H b) ∧
        IsLeaf H c ∧ IsLeaf H d) ∨
      (IsLeaf H a ∧ IsLeaf H b ∧
        (IsDiarySplit H c ∨ IsDiarySplit H d))) :
    (onePassRawTarget H).twoMeetLevel
      (onePassOldImage H a) (onePassOldImage H b)
      (onePassOldImage H c) (onePassOldImage H d) =
      onePassOldImage H (H.twoMeetLevel a b c d) := by
  classical
  let G := onePassRawTarget H
  let f := onePassOldImage H
  let w := H.twoMeetLevel a b c d
  let z := G.twoMeetLevel (f a) (f b) (f c) (f d)
  have hw3 : w < 3 :=
    P.cross_role_twoMeet_lt_three a b c d
      hab hcd ha3 hc3 hCases
  have hfAB : f a < f b := (onePassOldImage_strictMono H) hab
  have hfCD : f c < f d := (onePassOldImage_strictMono H) hcd
  have hCasesTarget :
      ((IsDiarySplit G (f a) ∨ IsDiarySplit G (f b)) ∧
        IsLeaf G (f c) ∧ IsLeaf G (f d)) ∨
      (IsLeaf G (f a) ∧ IsLeaf G (f b) ∧
        (IsDiarySplit G (f c) ∨ IsDiarySplit G (f d))) := by
    rcases hCases with ⟨hm, hc, hd⟩ | ⟨ha, hb, hm⟩
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · rcases hm with hma | hmb
        · exact Or.inl ((onePassOldImage_isDiarySplit H a).mp hma)
        · exact Or.inr ((onePassOldImage_isDiarySplit H b).mp hmb)
      · exact (onePassRawTarget_old_leaf_iff H c).mpr hc
      · exact (onePassRawTarget_old_leaf_iff H d).mpr hd
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · exact (onePassRawTarget_old_leaf_iff H a).mpr ha
      · exact (onePassRawTarget_old_leaf_iff H b).mpr hb
      · rcases hm with hmc | hmd
        · exact Or.inl ((onePassOldImage_isDiarySplit H c).mp hmc)
        · exact Or.inr ((onePassOldImage_isDiarySplit H d).mp hmd)
  have hfa3 : 3 ≤ f a := (onePassOldImage_ge_three_iff H a).mpr ha3
  have hfc3 : 3 ≤ f c := (onePassOldImage_ge_three_iff H c).mpr hc3
  have hz3 : z < 3 :=
    (onePassRawTarget_isPrediary P).cross_role_twoMeet_lt_three
      (f a) (f b) (f c) (f d)
      hfAB hfCD hfa3 hfc3 hCasesTarget
  have hAtSource := H.twoMeetLevel_agree a b c d
  have hAtTarget := G.twoMeetLevel_agree (f a) (f b) (f c) (f d)
  have hTargetW :
      G.SameTwoTypeBelow w (f a) (f b) (f c) (f d) :=
    (onePass_twoTypeBelow_markerCut_iff H w a b c d
      (by omega)).mp hAtSource
  have hSourceZ : H.SameTwoTypeBelow z a b c d :=
    (onePass_twoTypeBelow_markerCut_iff H z a b c d
      (by omega)).mpr hAtTarget
  have hwle : w ≤ z :=
    Nat.le_findGreatest (by omega : w ≤ min (f a) (f c)) hTargetW
  have hzle : z ≤ w :=
    Nat.le_findGreatest (by omega : z ≤ min a c) hSourceZ
  have heq : z = w := by omega
  calc
    G.twoMeetLevel (f a) (f b) (f c) (f d) = w := heq
    _ = f w := (onePassOldImage_fixed_below_three H w hw3).symm
    _ = f (H.twoMeetLevel a b c d) := rfl

end DiaryLeafPriority
end ThreeUniformDiaries
