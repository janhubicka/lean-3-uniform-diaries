import ThreeUniformDiaries.DiaryOnePassCodeEquivalence
import ThreeUniformDiaries.DiaryOnePassTerminalGerms

/-!
# The exact finite-code form of one-pass delayed pair tests

The static block construction labels each realised singleton type by
its finite Boolean word and each realised full pair type by its full
finite Boolean tuple. An old 2-type event on pair (q,u) can later
become a singleton coordinate for u when the old leaf q is reached.

For m <= q, this event's finite-code value factors through the
original singleton code of u over q+1, including the capped case
m=q. At the terminal cap q the dependence is an EQUIVALENCE:
the full pair codes of (q,u) and (q,v) at q are equal exactly when
their next singleton codes agree.

This is the codomain-level bridge needed for the first implication
in the one-pass prefix-transport induction. It does NOT establish
the global block construction, V/E/S, protected mixed meets or
flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- All finite full pair-germ codes with fixed first member q,
read at an earlier original cut m<=q, are determined by the
singleton code of their second member at q+1. -/
theorem fixedFirstTwoCode_eq_of_nextOneCode
    (H : Ordered3Graph Nat) (m q u v : Nat) (hmq : m ≤ q)
    (h : oneCode H (q + 1) u = oneCode H (q + 1) v) :
    twoCode H m q u = twoCode H m q v := by
  apply (twoCode_eq_iff_sameTwoType H m q u q v).mpr
  exact H.fixed_first_pair_type_of_one_type_succ m q u v hmq
    ((oneCode_eq_iff_sameOneType H (q + 1) u v).mp h)

/-- At the terminal cap, equality of the finite full pair codes
is EQUIVALENT to equality of the next singleton codes.
No positive/negative edge hypotheses or diary axioms are used. -/
theorem terminalTwoCode_eq_iff_nextOneCode
    (H : Ordered3Graph Nat) (q u v : Nat) :
    (twoCode H q q u = twoCode H q q v) ↔
      (oneCode H (q + 1) u = oneCode H (q + 1) v) := by
  exact (twoCode_eq_iff_sameTwoType H q q u q v).trans
    ((H.terminal_pair_type_iff_next_singleton q u v).trans
      (oneCode_eq_iff_sameOneType H (q + 1) u v).symm)

/-- Membership in any selected full pair-type code class at an
earlier cut m is constant on later leaves whose original
singleton types agree through q+1. This is the literal
independence-of-future-choice calculation for a delayed event. -/
theorem selectedFixedFirstPairCode_agrees
    (H : Ordered3Graph Nat) (m q a b u v : Nat)
    (hmq : m ≤ q)
    (h : oneCode H (q + 1) u = oneCode H (q + 1) v) :
    (twoCode H m q u = twoCode H m a b) ↔
      (twoCode H m q v = twoCode H m a b) := by
  rw [H.fixedFirstTwoCode_eq_of_nextOneCode m q u v hmq h]

end DiaryLeafPriority
end ThreeUniformDiaries
