import ThreeUniformDiaries.AuxTypes

/-!
# Static terminal and delayed pair-type factorisation

This file formalises the two nonlocal dependencies in the proposed
one-pass pre-diary completion proof, without assuming the full
completion construction.

An old 2-split event attached to a pair (q,u) at some earlier cut m
may become a singleton-type coordinate when the fixed leaf q arrives.
All tests at this event are functions of the ORIGINAL singleton
(q+1)-type of u.

In particular, two capped terminal pairs (q,u) and (q,v) which have
the same full pair type over q necessarily have second members
with the same original singleton type over q+1.

This is necessary to maintain the exact original-prefix partitions,
but does not establish the rest of the one-pass construction, the
relative protected-copy theorem or flip absorption.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Singleton agreement through cut q+1 determines the full
types of (q,u) and (q,v) at EVERY cut m <= q. This is the
delayed-test invariant needed when a 2-split event with
first pair member q later appears as a singleton coordinate. -/
theorem fixed_first_pair_type_of_one_type_succ
    (H : Ordered3Graph Nat) (m q u v : Nat)
    (hmq : m ≤ q)
    (huv : H.SameOneTypeBelow (q + 1) u v) :
    H.SameTwoTypeBelow m q u q v := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab hb
    rfl
  · intro a b hab hb
    exact huv hab (by omega)
  · intro a ha
    exact huv (by omega) (by omega)

/-- Old full pair-type equality of capped terminal pairs forces
their second members to have exactly the same singleton type
one level beyond the cap. The auxiliary test at cut q
supplies precisely the new singleton column indexed by q. -/
theorem terminal_pair_type_implies_next_singleton
    (H : Ordered3Graph Nat) (q u v : Nat)
    (h : H.SameTwoTypeBelow q q u q v) :
    H.SameOneTypeBelow (q + 1) u v := by
  intro a b hab hb
  by_cases hbm : b < q
  · exact h.2.1 hab hbm
  · have hbq : b = q := by omega
    subst b
    exact h.2.2 (by omega)

/-- The two statements combine to identify equality of full
terminal pair types at their cap with equality of the later
singleton types one level beyond that cap. -/
theorem terminal_pair_type_iff_next_singleton
    (H : Ordered3Graph Nat) (q u v : Nat) :
    H.SameTwoTypeBelow q q u q v ↔
      H.SameOneTypeBelow (q + 1) u v := by
  constructor
  · exact H.terminal_pair_type_implies_next_singleton q u v
  · exact H.fixed_first_pair_type_of_one_type_succ
      q q u v (le_refl q)

end Ordered3Graph
end ThreeUniformDiaries
