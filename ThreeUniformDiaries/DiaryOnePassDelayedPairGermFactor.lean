import ThreeUniformDiaries.DiaryOnePassEventReflection
import ThreeUniformDiaries.DiaryOnePassStaticCodeTransport

/-!
# Delayed one-type tests from earlier pair events

The one-pass target inserts 2-split events before each ORIGINAL vertex m.
A fresh edge (e, f(q), f(u)) then appears as a singleton-coordinate test
when the old leaf q becomes the middle vertex in a later column.

A priori these extra tests could destroy the original singleton type
partition, invalidate V3, and invalidate the proposed static block
transport. We prove the precise noninterference statement:

For m <= q, the ENTIRE original pair-germ code of (q,u) at m is
determined by the original singleton (q+1)-code of u. In particular,
the actual target edge (e,f(q),f(u)) is constant on every original
singleton type through cut q+1, independently of the selected event.

At the terminal cap m=q this code factorisation is an equivalence.
No V/E/S completion or global prefix induction is asserted here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- The COMPLETE selected pair germ at an earlier cut m<=q
is determined by the next singleton code of its later member.

If m=q, the germ is terminal and has no successor two-code.
If m<q, both m and m+1 pair codes factor through the same
singleton code at q+1. -/
theorem fixedFirstTwoGerm_eq_of_nextOneCode
    (H : Ordered3Graph Nat) (m q u v : Nat)
    (hmq : m ≤ q)
    (hcode : oneCode H (q + 1) u = oneCode H (q + 1) v) :
    twoGermCode H m q u = twoGermCode H m q v := by
  have hp : twoCode H m q u = twoCode H m q v :=
    fixedFirstTwoCode_eq_of_nextOneCode H m q u v hmq hcode
  change
    (twoCode H m q u,
      if q = m then none else some (twoCode H (m + 1) q u)) =
    (twoCode H m q v,
      if q = m then none else some (twoCode H (m + 1) q v))
  apply Prod.ext
  · exact hp
  · by_cases hcap : q = m
    · simp [hcap]
    · have hnext : m + 1 ≤ q := by omega
      have hs : twoCode H (m + 1) q u = twoCode H (m + 1) q v :=
        fixedFirstTwoCode_eq_of_nextOneCode
          H (m + 1) q u v hnext hcode
      simp [hcap, hs]

/-- At a terminal cap the finite full pair germ of (q,u)
contains EXACTLY the next singleton code of u, including the
reverse implication. -/
theorem terminalTwoGerm_eq_iff_nextOneCode
    (H : Ordered3Graph Nat) (q u v : Nat) :
    (twoGermCode H q q u = twoGermCode H q q v) ↔
      (oneCode H (q + 1) u = oneCode H (q + 1) v) := by
  exact (twoGerm_terminal_eq_iff_parent H q u v).trans
    ((H.terminal_pair_type_iff_next_singleton q u v).trans
      (oneCode_eq_iff_sameOneType H (q + 1) u v).symm)

/-- Every selected pair-germ class test on pairs with fixed
first member q is constant on the NEXT original singleton
(q+1)-code of the second member. -/
theorem fixedFirstSelectedGermBit_agrees
    (H : Ordered3Graph Nat) (m q u v : Nat)
    (g : TwoGermSpace m) (hmq : m ≤ q)
    (hcode : oneCode H (q + 1) u = oneCode H (q + 1) v) :
    (twoGermCode H m q u = g) ↔
      (twoGermCode H m q v = g) := by
  rw [fixedFirstTwoGerm_eq_of_nextOneCode H m q u v hmq hcode]

/-- The key concrete delayed-test invariant:
an EARLIER inserted pair-event edge becomes a singleton test
at original leaf q, but it cannot distinguish later leaves
having the same original singleton code through q+1.

This is a statement about the actual target hyperedges, using
the exact event-reflection theorem, not an abstract class indicator. -/
theorem onePassPairEvent_delayed_singleton_test_agrees
    (H : Ordered3Graph Nat) (m q u v : Nat)
    (i : Fin (onePassBlock H m).length)
    (g : TwoGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.pair m g)
    (hmq : m ≤ q) (hqu : q < u) (hqv : q < v)
    (hq : IsLeaf H q) (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hcode : oneCode H (q + 1) u = oneCode H (q + 1) v) :
    ((onePassRawTarget H).edge
      (onePassEventPosition H m i)
      (onePassOldImage H q) (onePassOldImage H u)) ↔
    ((onePassRawTarget H).edge
      (onePassEventPosition H m i)
      (onePassOldImage H q) (onePassOldImage H v)) := by
  have hgem : twoGermCode H m q u = twoGermCode H m q v :=
    fixedFirstTwoGerm_eq_of_nextOneCode H m q u v hmq hcode
  have heU := onePassRawTarget_pair_incidence_iff H m q u i g hget
  have heV := onePassRawTarget_pair_incidence_iff H m q v i g hget
  have hU : (onePassRawTarget H).edge (onePassEventPosition H m i)
        (onePassOldImage H q) (onePassOldImage H u) ↔
      twoGermCode H m q u = g := by
    simpa only [hq, hu, hmq, hqu, true_and] using heU
  have hV : (onePassRawTarget H).edge (onePassEventPosition H m i)
        (onePassOldImage H q) (onePassOldImage H v) ↔
      twoGermCode H m q v = g := by
    simpa only [hq, hv, hmq, hqv, true_and] using heV
  have hs : (twoGermCode H m q u = g) ↔
      (twoGermCode H m q v = g) := by
    rw [hgem]
  exact hU.trans (hs.trans hV.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
