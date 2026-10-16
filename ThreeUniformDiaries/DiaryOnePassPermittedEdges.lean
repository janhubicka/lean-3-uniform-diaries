import ThreeUniformDiaries.DiaryOnePassExactFreshRoles
import ThreeUniformDiaries.DiaryPrediaryDefinition

/-!
# Exact preservation of old roles and all permitted edge shapes

The static one-pass target is built directly from the input predirectory:
all original edges are copied by the strictly increasing old-vertex map;
all other edges have one new event vertex, which is a genuine 1-split
or 2-split according to the unique original germ label.

In this module we prove:
* the old-vertex map reflects and preserves all three literal
  marker-defined roles, even when comparing an old index below 3;
* the full E1--E5 permitted-edge *classification* of the actual
  target, assuming only RolePrediary of the input.

The target's V1/V2/V3, S1/S2, and all-role coverage remain separate.
-/


namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- Old vertices stay after the first three markers iff the
original vertex was after those markers. -/
theorem onePassOldImage_ge_three_iff
    (H : Ordered3Graph Nat) (u : Nat) :
    3 ≤ onePassOldImage H u ↔ 3 ≤ u := by
  constructor
  · intro h
    by_contra hu
    have hle : u ≤ 2 := by omega
    have hmap := (onePassOldImage_strictMono H).monotone hle
    rw [onePassOldImage_two] at hmap
    omega
  · intro h
    have hlt : 2 < u := by omega
    have hmap := (onePassOldImage_strictMono H) hlt
    rw [onePassOldImage_two] at hmap
    omega

/-- Because the old image is increasing and fixes the markers,
an old vertex has image 0 precisely when it is 0. -/
theorem onePassOldImage_eq_zero_iff
    (H : Ordered3Graph Nat) (u : Nat) :
    onePassOldImage H u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have heq : onePassOldImage H u = onePassOldImage H 0 := by
      simpa only [onePassOldImage_zero] using h
    exact (onePassOldImage_strictMono H).injective heq
  · rintro rfl
    exact onePassOldImage_zero H

theorem onePassOldImage_eq_one_iff
    (H : Ordered3Graph Nat) (u : Nat) :
    onePassOldImage H u = 1 ↔ u = 1 := by
  constructor
  · intro h
    have heq : onePassOldImage H u = onePassOldImage H 1 := by
      simpa only [onePassOldImage_one] using h
    exact (onePassOldImage_strictMono H).injective heq
  · rintro rfl
    exact onePassOldImage_one H

theorem onePassOldImage_eq_two_iff
    (H : Ordered3Graph Nat) (u : Nat) :
    onePassOldImage H u = 2 ↔ u = 2 := by
  constructor
  · intro h
    have heq : onePassOldImage H u = onePassOldImage H 2 := by
      simpa only [onePassOldImage_two] using h
    exact (onePassOldImage_strictMono H).injective heq
  · rintro rfl
    exact onePassOldImage_two H

/-- The input leaf role is preserved AND reflected at every old
vertex, including vertices below the three distinguished markers. -/
theorem onePassRawTarget_old_leaf_iff
    (H : Ordered3Graph Nat) (u : Nat) :
    IsLeaf (onePassRawTarget H) (onePassOldImage H u) ↔ IsLeaf H u := by
  simp only [IsLeaf, onePassOldImage_ge_three_iff,
    onePassRawTarget_old_marker_one_iff,
    onePassRawTarget_old_marker_two_iff]

theorem onePassRawTarget_old_oneSplit_iff
    (H : Ordered3Graph Nat) (u : Nat) :
    IsOneSplit (onePassRawTarget H) (onePassOldImage H u) ↔
      IsOneSplit H u := by
  simp only [IsOneSplit, onePassOldImage_ge_three_iff,
    onePassRawTarget_old_marker_one_iff,
    onePassRawTarget_old_marker_two_iff]

theorem onePassRawTarget_old_twoSplit_iff
    (H : Ordered3Graph Nat) (u : Nat) :
    IsTwoSplit (onePassRawTarget H) (onePassOldImage H u) ↔
      IsTwoSplit H u := by
  simp only [IsTwoSplit, onePassOldImage_ge_three_iff,
    onePassRawTarget_old_marker_one_iff,
    onePassRawTarget_old_marker_two_iff]

/-- Each permitted input edge remains a permitted edge of the
target: all five cases transfer under the induced old copy. -/
theorem onePassRawTarget_old_permitted
    (H : Ordered3Graph Nat) (a b c : Nat)
    (hp : PermittedDiaryEdge H a b c) :
    PermittedDiaryEdge (onePassRawTarget H)
      (onePassOldImage H a)
      (onePassOldImage H b)
      (onePassOldImage H c) := by
  rcases hp with hRole | hOne | hTwo | hDevlin | hNormal
  · rcases hRole with ⟨ha,hb,hc⟩
    apply Or.inl
    refine ⟨(onePassOldImage_eq_zero_iff H a).mpr ha, ?_,
      (onePassOldImage_ge_three_iff H c).mpr hc⟩
    rcases hb with hb | hb
    · exact Or.inl ((onePassOldImage_eq_one_iff H b).mpr hb)
    · exact Or.inr ((onePassOldImage_eq_two_iff H b).mpr hb)
  · rcases hOne with ⟨ha,hb,hc⟩
    exact Or.inr (Or.inl
      ⟨(onePassOldImage_eq_zero_iff H a).mpr ha,
       (onePassRawTarget_old_oneSplit_iff H b).mpr hb,
       (onePassRawTarget_old_leaf_iff H c).mpr hc⟩)
  · rcases hTwo with ⟨ha,hb,hc⟩
    exact Or.inr (Or.inr (Or.inl
      ⟨(onePassRawTarget_old_twoSplit_iff H a).mpr ha,
       (onePassRawTarget_old_leaf_iff H b).mpr hb,
       (onePassRawTarget_old_leaf_iff H c).mpr hc⟩))
  · rcases hDevlin with ⟨ha,hb,hc⟩
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    refine ⟨?_, (onePassRawTarget_old_leaf_iff H b).mpr hb,
      (onePassRawTarget_old_leaf_iff H c).mpr hc⟩
    rcases ha with ha | ha
    · exact Or.inl ((onePassOldImage_eq_one_iff H a).mpr ha)
    · exact Or.inr ((onePassOldImage_eq_two_iff H a).mpr ha)
  · rcases hNormal with ⟨ha,hb,hc⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨(onePassRawTarget_old_leaf_iff H a).mpr ha,
       (onePassRawTarget_old_leaf_iff H b).mpr hb,
       (onePassRawTarget_old_leaf_iff H c).mpr hc⟩)))

/-- Every increasing edge in the actual raw target has an E1--E5
permitted shape, assuming precisely the input pre-diary E axiom.
In particular inserted edges do not require any temporary state
or unverified target meet axiom. -/
theorem onePassRawTarget_permitted_edge
    {H : Ordered3Graph Nat} (P : RolePrediary H)
    (x y z : Nat) (he : (onePassRawTarget H).edge x y z) :
    PermittedDiaryEdge (onePassRawTarget H) x y z := by
  rcases he with hOld | hNew
  · obtain ⟨a,b,c,habc,rfl,rfl,rfl⟩ := hOld
    exact onePassRawTarget_old_permitted H a b c
      (P.permitted_edge a b c habc)
  · obtain ⟨m,i,_,hOne|hTwo⟩ := hNew
    · obtain ⟨g,hget,hMarker|hInc⟩ := hOne
      · obtain ⟨rfl,rfl,rfl⟩ := hMarker
        exact Or.inl ⟨rfl, Or.inl rfl,
          onePassEventPosition_ge_three H m i⟩
      · obtain ⟨u,hu,hmu,hcode,rfl,rfl,rfl⟩ := hInc
        exact Or.inr (Or.inl
          ⟨rfl, onePassRawTarget_fresh_oneSplit H m i g hget,
           (onePassRawTarget_old_leaf_iff H u).mpr hu⟩)
    · obtain ⟨g,hget,hMarker|hInc⟩ := hTwo
      · obtain ⟨rfl,rfl,rfl⟩ := hMarker
        exact Or.inl ⟨rfl, Or.inr rfl,
          onePassEventPosition_ge_three H m i⟩
      · obtain ⟨u,v,hu,hv,hmu,huv,hcode,rfl,rfl,rfl⟩ := hInc
        exact Or.inr (Or.inr (Or.inl
          ⟨onePassRawTarget_fresh_twoSplit H m i g hget,
           (onePassRawTarget_old_leaf_iff H u).mpr hu,
           (onePassRawTarget_old_leaf_iff H v).mpr hv⟩))

end DiaryLeafPriority
end ThreeUniformDiaries
