import ThreeUniformDiaries.DiaryOnePassConcreteCarrier
import Lean.Elab.Tactic.Omega

/-!
# Track B: exact obstacle to preserving a literal prefix in one-pass completion

The verified static one-pass completion enumerates finite event blocks
BEFORE each old original vertex m. Hence the old-image rank is

  onePassOldImage H m = m + sum_{i<m} blockSize(i) + blockSize(m).

The exact (not merely sufficient) condition for every old rank below
p to remain literally fixed is: NO one-pass event occurs at ANY
original level m<p. A positive event block at such a level
necessarily moves its original vertex and invalidates literal
old-prefix protection.

If the event-free condition holds, the ACTUAL raw one-pass target
retains the entire old increasing edge AND nonedge table literally
on the protected prefix; this follows from the already verified
induced old-copy edge iff.

This is a precise interface for the still OPEN relative strong
absorber extension: the old finite copy must be placed in an
ambient pre-diary whose event schedule has no insertion before
the chosen proper protected cut. No theorem constructs such a
prediary, no full finite end extension, no selected bounded ranks,
and no countable every-target-flip absorption are claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A concrete and finite-cut property of the actual static
one-pass construction: no selected singleton or pair events are
inserted before ANY original position in [0,p). -/
def OnePassNoEventsBelow
    (H : Ordered3Graph Nat) (p : Nat) : Prop :=
  ∀ m : Nat, m < p → onePassBlockSize H m = 0

/-- Exact necessary-and-sufficient condition for the actual
one-pass old-vertex map to preserve a full numerical prefix
LITERALLY, rather than merely preserving the induced relation
along a shifted copy. -/
theorem onePassOldImage_fixed_prefix_iff_noEvents
    (H : Ordered3Graph Nat) (p : Nat) :
    (∀ m : Nat, m < p → onePassOldImage H m = m) ↔
      OnePassNoEventsBelow H p := by
  constructor
  · intro hFix m hm
    have heq := hFix m hm
    change m + (∑ i ∈ Finset.range m, onePassBlockSize H i) +
      onePassBlockSize H m = m at heq
    omega
  · intro hNo m hm
    have hSum : (∑ i ∈ Finset.range m, onePassBlockSize H i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hNo i (lt_trans (Finset.mem_range.mp hi) hm)
    change m + (∑ i ∈ Finset.range m, onePassBlockSize H i) +
      onePassBlockSize H m = m
    rw [hSum, hNo m hm]
    omega

/-- Even one genuine scheduled event at an old protected vertex
strictly moves that old numerical rank. In particular, future
completions cannot repair this by finite-support compression alone. -/
theorem onePassOldImage_moves_of_nonzeroBlock
    (H : Ordered3Graph Nat) (m : Nat)
    (hEvent : 0 < onePassBlockSize H m) :
    m < onePassOldImage H m := by
  change m < m + (∑ i ∈ Finset.range m, onePassBlockSize H i) +
      onePassBlockSize H m
  omega

/-- No event on the protected prefix gives the literal complete
edge AND nonedge table of the original source on that prefix,
using the verified one-pass induced-copy theorem. -/
theorem onePassRawTarget_edge_iff_on_noEvent_prefix
    (H : Ordered3Graph Nat) (p : Nat)
    (hNo : OnePassNoEventsBelow H p)
    (a b c : Nat) (ha : a < p) (hb : b < p) (hc : c < p) :
    (onePassRawTarget H).edge a b c ↔ H.edge a b c := by
  have hFix :=
    (onePassOldImage_fixed_prefix_iff_noEvents H p).mpr hNo
  have h := onePassRawTarget_edge_image_iff H a b c
  simpa only [hFix a ha, hFix b hb, hFix c hc] using h

end DiaryLeafPriority
end ThreeUniformDiaries
