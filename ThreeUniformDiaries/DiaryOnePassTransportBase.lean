import ThreeUniformDiaries.DiaryOnePassRoleCoverage

/-!
# Exact transport at the initial marker cut of one-pass completion

The proposed one-pass finite-cut induction starts immediately before
the first event block B_3. No event has been added at marker levels
0,1,2, and the concrete old-vertex map fixes those markers exactly.

Using only the ACTUAL induced old-copy edge equivalence, we prove
that singleton, auxiliary and complete ordered pair-type AGREEMENT
below cut 3 is preserved AND REFLECTED by the new target.

These statements hold for arbitrary original vertices/pairs, not just
leaves, and need no V/E/S hypotheses or artificial type code
realizations. They constitute the actual base case for the global
source-cut type transport induction. The successor step is open.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- Every original vertex below the first event cut 3 is
fixed literally by the one-pass embedding. -/
theorem onePassOldImage_fixed_below_three
    (H : Ordered3Graph Nat) (a : Nat) (ha : a < 3) :
    onePassOldImage H a = a := by
  have hCases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases hCases with h0 | h1 | h2
  · subst a
    exact onePassOldImage_zero H
  · subst a
    exact onePassOldImage_one H
  · subst a
    exact onePassOldImage_two H

/-- Exact source/target equality of singleton-type AGREEMENT
through marker cut 3. -/
theorem onePass_oneTypeBelow_three_iff
    (H : Ordered3Graph Nat) (u v : Nat) :
    H.SameOneTypeBelow 3 u v ↔
      (onePassRawTarget H).SameOneTypeBelow 3
        (onePassOldImage H u) (onePassOldImage H v) := by
  constructor
  · intro hs a b hab hb
    have ha : a < 3 := lt_trans hab hb
    have hu := onePassRawTarget_edge_image_iff H a b u
    have hv := onePassRawTarget_edge_image_iff H a b v
    rw [onePassOldImage_fixed_below_three H a ha,
        onePassOldImage_fixed_below_three H b hb] at hu hv
    exact hu.trans ((hs hab hb).trans hv.symm)
  · intro ht a b hab hb
    have ha : a < 3 := lt_trans hab hb
    have hu := onePassRawTarget_edge_image_iff H a b u
    have hv := onePassRawTarget_edge_image_iff H a b v
    rw [onePassOldImage_fixed_below_three H a ha,
        onePassOldImage_fixed_below_three H b hb] at hu hv
    exact hu.symm.trans ((ht hab hb).trans hv)

/-- Exact transport of the auxiliary coordinate tests of TWO
ordered pairs at the initial marker cut. -/
theorem onePass_auxTypeBelow_three_iff
    (H : Ordered3Graph Nat) (u₀ u₁ v₀ v₁ : Nat) :
    H.SameAuxTypeBelow 3 u₀ u₁ v₀ v₁ ↔
      (onePassRawTarget H).SameAuxTypeBelow 3
        (onePassOldImage H u₀) (onePassOldImage H u₁)
        (onePassOldImage H v₀) (onePassOldImage H v₁) := by
  constructor
  · intro hs a ha
    have hu := onePassRawTarget_edge_image_iff H a u₀ u₁
    have hv := onePassRawTarget_edge_image_iff H a v₀ v₁
    rw [onePassOldImage_fixed_below_three H a ha] at hu hv
    exact hu.trans ((hs ha).trans hv.symm)
  · intro ht a ha
    have hu := onePassRawTarget_edge_image_iff H a u₀ u₁
    have hv := onePassRawTarget_edge_image_iff H a v₀ v₁
    rw [onePassOldImage_fixed_below_three H a ha] at hu hv
    exact hu.symm.trans ((ht ha).trans hv)

/-- The FULL two-type (both singleton components and auxiliary
edge tests) has the exact same partition before B_3. -/
theorem onePass_twoTypeBelow_three_iff
    (H : Ordered3Graph Nat) (u₀ u₁ v₀ v₁ : Nat) :
    H.SameTwoTypeBelow 3 u₀ u₁ v₀ v₁ ↔
      (onePassRawTarget H).SameTwoTypeBelow 3
        (onePassOldImage H u₀) (onePassOldImage H u₁)
        (onePassOldImage H v₀) (onePassOldImage H v₁) := by
  change
    (H.SameOneTypeBelow 3 u₀ v₀ ∧
     H.SameOneTypeBelow 3 u₁ v₁ ∧
     H.SameAuxTypeBelow 3 u₀ u₁ v₀ v₁) ↔
    ((onePassRawTarget H).SameOneTypeBelow 3
       (onePassOldImage H u₀) (onePassOldImage H v₀) ∧
     (onePassRawTarget H).SameOneTypeBelow 3
       (onePassOldImage H u₁) (onePassOldImage H v₁) ∧
     (onePassRawTarget H).SameAuxTypeBelow 3
       (onePassOldImage H u₀) (onePassOldImage H u₁)
       (onePassOldImage H v₀) (onePassOldImage H v₁))
  rw [onePass_oneTypeBelow_three_iff H u₀ v₀,
      onePass_oneTypeBelow_three_iff H u₁ v₁,
      onePass_auxTypeBelow_three_iff H u₀ u₁ v₀ v₁]

end DiaryLeafPriority
end ThreeUniformDiaries
