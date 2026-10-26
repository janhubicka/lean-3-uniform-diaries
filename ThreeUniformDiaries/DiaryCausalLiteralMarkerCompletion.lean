import ThreeUniformDiaries.DiaryCausalMarkerTypeTransport

/-!
# Construct a literal-V3-compatible causal marker extension

The formula for a missing off-branch Devlin marker refers to the
FINAL graph's LexEarlier comparator, and so looks recursive.
The previously verified middle-column causality lemma removes
this difficulty: LexEarlier(y,z) only reads columns with middle
coordinate STRICTLY BELOW y, provided y<z.

Build a sequence of ternary relations by scanning middle vertices
y=0,1,2,... and adding marker-1/marker-2 incidences in column y
using the graph obtained at stage y. The new edges are supported
at that column alone. Once a column has been passed, later stages
do not change it; the final graph is read at stage y+1 in
column y.

This proves an actual fixed point for the LITERAL V3 marker
equations for any mask supported on increasing (middle,last)
pairs. The input raw edges are preserved. If the raw relation
has no marker edges on the masked pairs, the resulting output
has exactly the required complementary marker bits there.

This is NOT a pre-diary construction by itself. Original-branch
marker incidences, V1/V2 and protected numerical meets still
require the separate sign-rooted geometric application.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Add only new marker incidences at a single middle column y,
using the literal lexicographic comparator of the previous stage. -/
noncomputable def causalMarkerStep
    (G : Ordered3Graph Nat) (mask : Nat → Nat → Prop)
    (k : Nat) : Ordered3Graph Nat where
  edge x y z :=
    G.edge x y z ∨
      (y = k ∧ x = 1 ∧ mask y z ∧ LexEarlier G y z) ∨
      (y = k ∧ x = 2 ∧ mask y z ∧ ¬ LexEarlier G y z)

/-- The iterative scan: stage k has made all choices in
middle columns 0,...,k-1, but not in column k. -/
noncomputable def causalMarkerStages
    (R : Ordered3Graph Nat) (mask : Nat → Nat → Prop) :
    Nat → Ordered3Graph Nat
  | 0 => R
  | k + 1 => causalMarkerStep (causalMarkerStages R mask k) mask k

/-- Applying stage k does not change any different middle column. -/
theorem causalMarkerStep_middle_ne
    (G : Ordered3Graph Nat) (mask : Nat → Nat → Prop)
    (k x y z : Nat) (hy : y ≠ k) :
    (causalMarkerStep G mask k).edge x y z ↔ G.edge x y z := by
  change
    (G.edge x y z ∨
      (y = k ∧ x = 1 ∧ mask y z ∧ LexEarlier G y z) ∨
      (y = k ∧ x = 2 ∧ mask y z ∧ ¬ LexEarlier G y z)) ↔
      G.edge x y z
  simp [hy]

/-- Before stage t reaches middle column y >= t, that column
is still exactly the original raw column. -/
theorem causalMarkerStages_future_raw
    (R : Ordered3Graph Nat) (mask : Nat → Nat → Prop)
    (t : Nat) :
    ∀ y : Nat, t ≤ y → ∀ x z : Nat,
      (causalMarkerStages R mask t).edge x y z ↔
        R.edge x y z := by
  induction t with
  | zero =>
      intro y h x z
      exact Iff.rfl
  | succ t ih =>
      intro y hty x z
      have hy : y ≠ t := by omega
      have hStep := causalMarkerStep_middle_ne
        (causalMarkerStages R mask t) mask t x y z hy
      exact hStep.trans (ih y (by omega) x z)

/-- After column y has been processed, every later stage
has exactly the same complete column y (all first/last coordinates). -/
theorem causalMarkerStages_stable_column
    (R : Ordered3Graph Nat) (mask : Nat → Nat → Prop)
    (b : Nat) :
    ∀ y : Nat, y < b → ∀ x z : Nat,
      (causalMarkerStages R mask b).edge x y z ↔
        (causalMarkerStages R mask (y + 1)).edge x y z := by
  induction b with
  | zero =>
      intro y hy
      omega
  | succ b ih =>
      intro y hy x z
      by_cases hEq : y = b
      · subst y
        exact Iff.rfl
      · have hyb : y < b := by omega
        have hStep := causalMarkerStep_middle_ne
          (causalMarkerStages R mask b) mask b x y z hEq
        exact hStep.trans (ih y hyb x z)

/-- Read each middle column of the infinite resulting graph
from the first stage at which that column has been processed. -/
noncomputable def causalMarkerLimit
    (R : Ordered3Graph Nat) (mask : Nat → Nat → Prop) :
    Ordered3Graph Nat where
  edge x y z := (causalMarkerStages R mask (y + 1)).edge x y z

/-- The graph available when column y is processed and the
final output agree on ALL earlier middle columns. -/
theorem causalMarkerStages_agree_limit_below
    (R : Ordered3Graph Nat) (mask : Nat → Nat → Prop)
    (y : Nat) :
    MiddleColumnAgreementBelow
      (causalMarkerStages R mask y)
      (causalMarkerLimit R mask) y := by
  intro x m z hmy
  exact causalMarkerStages_stable_column R mask y m hmy x z

/-- Existence of a literal self-consistent V3 marker choice.

For increasing masked pairs y<z, the stage-y decision
LexEarlier(stage y,y,z) is EQUAL to the decision made in
the final graph: all lower middle columns already agree.

The output therefore satisfies the *final-graph* marker
formula, not a synthetic stage-relative replacement. -/
theorem causalMarkerLimit_formula
    (R : Ordered3Graph Nat) (mask : Nat → Nat → Prop)
    (hMaskLater : ∀ y z, mask y z → y < z)
    (x y z : Nat) :
    (causalMarkerLimit R mask).edge x y z ↔
      CausalMarkerColumn R (causalMarkerLimit R mask) mask x y z := by
  have hRaw : (causalMarkerStages R mask y).edge x y z ↔
      R.edge x y z :=
    causalMarkerStages_future_raw R mask y y le_rfl x z
  have hMaskedLex :
      (mask y z ∧
        LexEarlier (causalMarkerStages R mask y) y z) ↔
      (mask y z ∧
        LexEarlier (causalMarkerLimit R mask) y z) := by
    by_cases hm : mask y z
    · have hLex := middleColumn_lexEarlier_iff
        (causalMarkerStages R mask y)
        (causalMarkerLimit R mask)
        y z (hMaskLater y z hm)
        (causalMarkerStages_agree_limit_below R mask y)
      exact and_congr Iff.rfl hLex
    · simp [hm]
  have hMaskedNotLex :
      (mask y z ∧
        ¬ LexEarlier (causalMarkerStages R mask y) y z) ↔
      (mask y z ∧
        ¬ LexEarlier (causalMarkerLimit R mask) y z) := by
    by_cases hm : mask y z
    · have hLex := middleColumn_lexEarlier_iff
        (causalMarkerStages R mask y)
        (causalMarkerLimit R mask)
        y z (hMaskLater y z hm)
        (causalMarkerStages_agree_limit_below R mask y)
      exact and_congr Iff.rfl (not_congr hLex)
    · simp [hm]
  have hOne :
      (x = 1 ∧ mask y z ∧
        LexEarlier (causalMarkerStages R mask y) y z) ↔
      (x = 1 ∧ mask y z ∧
        LexEarlier (causalMarkerLimit R mask) y z) :=
    and_congr Iff.rfl hMaskedLex
  have hTwo :
      (x = 2 ∧ mask y z ∧
        ¬ LexEarlier (causalMarkerStages R mask y) y z) ↔
      (x = 2 ∧ mask y z ∧
        ¬ LexEarlier (causalMarkerLimit R mask) y z) :=
    and_congr Iff.rfl hMaskedNotLex
  have hWhole :
      ((causalMarkerStages R mask y).edge x y z ∨
        (x = 1 ∧ mask y z ∧
          LexEarlier (causalMarkerStages R mask y) y z) ∨
        (x = 2 ∧ mask y z ∧
          ¬ LexEarlier (causalMarkerStages R mask y) y z)) ↔
      (R.edge x y z ∨
        (x = 1 ∧ mask y z ∧
          LexEarlier (causalMarkerLimit R mask) y z) ∨
        (x = 2 ∧ mask y z ∧
          ¬ LexEarlier (causalMarkerLimit R mask) y z)) :=
    or_congr hRaw (or_congr hOne hTwo)
  change
    ((causalMarkerStages R mask y).edge x y z ∨
      (y = y ∧ x = 1 ∧ mask y z ∧
        LexEarlier (causalMarkerStages R mask y) y z) ∨
      (y = y ∧ x = 2 ∧ mask y z ∧
        ¬ LexEarlier (causalMarkerStages R mask y) y z)) ↔
    (R.edge x y z ∨
      (x = 1 ∧ mask y z ∧
        LexEarlier (causalMarkerLimit R mask) y z) ∨
      (x = 2 ∧ mask y z ∧
        ¬ LexEarlier (causalMarkerLimit R mask) y z))
  simpa using hWhole

/-- The literal marker equations have an actual graph solution,
without any global prefix-uniform orientation postulate. -/
theorem exists_causalMarker_literal_fixedPoint
    (R : Ordered3Graph Nat) (mask : Nat → Nat → Prop)
    (hMaskLater : ∀ y z, mask y z → y < z) :
    ∃ G : Ordered3Graph Nat,
      ∀ x y z : Nat,
        G.edge x y z ↔ CausalMarkerColumn R G mask x y z := by
  exact ⟨causalMarkerLimit R mask,
    causalMarkerLimit_formula R mask hMaskLater⟩

/-- On a masked pair with no raw marker-one edge, the final
marker-one bit is EXACTLY the literal LexEarlier value. -/
theorem causalMarkerLimit_marker_one
    (R : Ordered3Graph Nat) (mask : Nat → Nat → Prop)
    (hMaskLater : ∀ y z, mask y z → y < z)
    (y z : Nat) (hm : mask y z)
    (hRaw : ¬ R.edge 1 y z) :
    (causalMarkerLimit R mask).edge 1 y z ↔
      LexEarlier (causalMarkerLimit R mask) y z := by
  have hForm := causalMarkerLimit_formula
    R mask hMaskLater 1 y z
  simp only [CausalMarkerColumn] at hForm
  simpa [hm, hRaw] using hForm

/-- On a masked pair with no raw marker-two edge, the
second Devlin marker is the complement of the first. -/
theorem causalMarkerLimit_marker_two
    (R : Ordered3Graph Nat) (mask : Nat → Nat → Prop)
    (hMaskLater : ∀ y z, mask y z → y < z)
    (y z : Nat) (hm : mask y z)
    (hRaw : ¬ R.edge 2 y z) :
    (causalMarkerLimit R mask).edge 2 y z ↔
      ¬ LexEarlier (causalMarkerLimit R mask) y z := by
  have hForm := causalMarkerLimit_formula
    R mask hMaskLater 2 y z
  simp only [CausalMarkerColumn] at hForm
  simpa [hm, hRaw] using hForm

/-- The causal extension retains the increasing-edge
condition whenever the original graph has it and all
masked pairs are actual later leaves (middle >= 3). -/
theorem causalMarkerLimit_edges_increasing
    (R : Ordered3Graph Nat) (mask : Nat → Nat → Prop)
    (hRawOrdered : ∀ x y z, R.edge x y z → x < y ∧ y < z)
    (hMaskSupported : ∀ y z, mask y z → 3 ≤ y ∧ y < z)
    (x y z : Nat)
    (he : (causalMarkerLimit R mask).edge x y z) :
    x < y ∧ y < z := by
  have hFormula :=
    (causalMarkerLimit_formula R mask
      (fun y z hm => (hMaskSupported y z hm).2)
      x y z).mp he
  rcases hFormula with hOld | ⟨hx,hm,_⟩ | ⟨hx,hm,_⟩
  · exact hRawOrdered x y z hOld
  · have hSupported := hMaskSupported y z hm
    constructor
    · omega
    · exact hSupported.2
  · have hSupported := hMaskSupported y z hm
    constructor
    · omega
    · exact hSupported.2

end DiaryLeafPriority
end ThreeUniformDiaries
