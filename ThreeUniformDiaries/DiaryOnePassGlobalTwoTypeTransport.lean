import ThreeUniformDiaries.DiaryOnePassOldLeafTwoTypeTransfer
import ThreeUniformDiaries.DiaryOnePassOriginalOneSplitTwoTypeTransfer
import ThreeUniformDiaries.DiaryOnePassOriginalSplitTransfer
import ThreeUniformDiaries.DiaryOnePassTransportBase

/-!
# Global full pair-type transport across all ORIGINAL one-pass cuts

For every original cut m>=3 and all ordered pairs (a,b),(c,d) of
original LEAVES whose first members are at least m, exact equality of
their SOURCE FULL two-types below m is equivalent to exact equality
of the actual target full two-types below the START of block B_m.

This is the complete two-type analogue of the independently
validated global singleton-type transport theorem. The proof is
induction on ORIGINAL source m (never a moving target index).
At the original vertex m there are exactly three cases:

* original LEAF: pair events plus singleton events in B_m reproduce
  the true source full successor type; delayed pair-event edges in
  the original leaf column are constant on these classes, and
  the copied old leaf edge (m,a,b) is already determined by the
  source next full pair type;
* original 1-SPLIT: the block contains only pair events, refining
  full types by exactly their source normal-pair germs; the old
  1-split then adds only original zero-marker coordinate tests
  already decided by source next full type;
* original 2-SPLIT: its B_m is empty, and the old 2-split adds just
  the copied auxiliary pair incidence bit (m,a,b).

The base at marker cut 3, all finite block edge tests and each
original vertex role are the actual checked concrete target facts.

This proof uses only source pre-diary V/E, NOT S1/S2, and it is
carefully restricted to original leaves/pairs with their first
members above the original cut. It does not imply universal
preservation at each old leaf image (the false printed lemma).
The target's full V1/V2/V3 and S1/S2 axioms, protected mixed meets,
finite diary interface and flip absorption remain separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Exact one-step full ordered-pair type transport, from the start
of B_m to the start of B_(m+1), for source leaf pairs strictly
above the original cut m. -/
theorem onePass_twoType_originalCut_succ
    (P : RolePrediary H) (m a b c d : Nat)
    (hm : 3 ≤ m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hab : a < b) (hcd : c < d)
    (hma : m < a) (hmc : m < c)
    (hBefore : H.SameTwoTypeBelow m a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassBefore H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d)) :
    H.SameTwoTypeBelow (m + 1) a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassBefore H (m + 1))
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  rw [onePassBefore_succ H m]
  rcases P.role_valid m hm with hLeaf | hOne | hTwo
  · exact onePass_original_leaf_twoType_transfer
      P m a b c d hLeaf ha hb hc hd hma hmc hab hcd hBefore
  · exact onePass_original_oneSplit_twoType_transfer
      P m a b c d hOne ha hb hc hd hma hmc hab hcd hBefore
  · have hNotLeaf : ¬ IsLeaf H m := by
      intro h
      exact h.2.2 hTwo.2.2
    have hNotSmall : ¬ m < 3 := by omega
    have hEmpty : onePassBlock H m = [] := by
      simp [onePassBlock, hNotSmall, hTwo, hNotLeaf]
    have hCut : onePassOldImage H m = onePassBefore H m := by
      simp [onePassOldImage, onePassBlockSize, hEmpty]
    have hBeforeOld :
        H.SameTwoTypeBelow m a b c d ↔
        (onePassRawTarget H).SameTwoTypeBelow
          (onePassOldImage H m)
          (onePassOldImage H a) (onePassOldImage H b)
          (onePassOldImage H c) (onePassOldImage H d) := by
      simpa only [hCut] using hBefore
    exact onePass_original_twoSplit_type_transfer
      P m a b c d hTwo hBeforeOld

/-- UNCONDITIONAL global full ordered-pair type transport for the
actual concrete one-pass target on all ORIGINAL source leaf pairs.
The target cut corresponding to source m is the START of its
finite event block B_m, never the cut after f(m). -/
theorem onePass_global_twoType_transport
    (P : RolePrediary H)
    (m a b c d : Nat)
    (hm : 3 ≤ m)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hab : a < b) (hcd : c < d)
    (hma : m ≤ a) (hmc : m ≤ c) :
    H.SameTwoTypeBelow m a b c d ↔
      (onePassRawTarget H).SameTwoTypeBelow
        (onePassBefore H m)
        (onePassOldImage H a) (onePassOldImage H b)
        (onePassOldImage H c) (onePassOldImage H d) := by
  have hAll :
      ∀ k : Nat, ∀ a b c d : Nat,
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        a < b → c < d →
        k + 3 ≤ a → k + 3 ≤ c →
        (H.SameTwoTypeBelow (k + 3) a b c d ↔
         (onePassRawTarget H).SameTwoTypeBelow
           (onePassBefore H (k + 3))
           (onePassOldImage H a) (onePassOldImage H b)
           (onePassOldImage H c) (onePassOldImage H d)) := by
    intro k
    induction k with
    | zero =>
      intro a b c d ha hb hc hd hab hcd hma hmc
      have hBefore3 : onePassBefore H 3 = 3 := by
        simpa using (onePassBefore_succ H 2)
      simpa only [Nat.zero_add, hBefore3] using
        (onePass_twoTypeBelow_three_iff H a b c d)
    | succ k ih =>
      intro a b c d ha hb hc hd hab hcd hma hmc
      have hPrev := ih a b c d
        ha hb hc hd hab hcd (by omega) (by omega)
      have hNext :=
        onePass_twoType_originalCut_succ P (k + 3)
          a b c d (by omega) ha hb hc hd
          hab hcd (by omega) (by omega) hPrev
      have hs : k + 3 + 1 = Nat.succ k + 3 := by omega
      simpa only [hs] using hNext
  have hIndex : m - 3 + 3 = m := by omega
  simpa only [hIndex] using
    (hAll (m - 3) a b c d
      ha hb hc hd hab hcd (by omega) (by omega))

end DiaryLeafPriority
end ThreeUniformDiaries
