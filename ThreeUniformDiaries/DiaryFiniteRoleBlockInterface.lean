import ThreeUniformDiaries.DiaryFiniteOrderedSumCarrier

/-!
# Finite V/E/S diary blocks, without false infinite-tail assumptions

A finite ordered ternary edge table is represented on Nat with all
its edges supported before a bound n. Beyond n the marker predicates
make vertices look like leaves, but no Devlin edges are provided.
Consequently a finite frame cannot be assumed to satisfy a global
RolePrediary or RoleDiary on all Nat. Earlier arguments carefully
kept their finite hypotheses explicit.

This module packages those hypotheses as a reusable *finite block*
interface for the two-block ordered sum and later finite iteration.

FiniteRolePrediaryBlock includes finite support, all genuine role
conditions, full E1--E5 edge shapes, V1/V2 positive-class coherence
and bounded genuine split witnesses, and the two Devlin marker
equivalences for ordered leaf pairs INSIDE the frame.

FiniteRoleDiaryBlock adds precisely the bounded S1/S2 meet clauses.
Neither definition asserts V/E/S outside the finite range.
The ordered sum should yield a finite pre-diary, not a full diary;
subsequent one-pass completion is an independent step.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- V/E finite pre-diary with all original split witnesses inside
the bounded edge frame. V1/V2 coherence can quantify over all Nat
because positive incidences automatically have bounded support,
whereas V3 must explicitly restrict to finite leaf pairs. -/
structure FiniteRolePrediaryBlock
    (H : Ordered3Graph Nat) (n : Nat) : Prop where
  frame : FiniteDiaryEdgeFrame H n
  role_valid :
    ∀ z : Nat, 3 ≤ z → z < n →
      IsLeaf H z ∨ IsOneSplit H z ∨ IsTwoSplit H z
  one_split_coherent :
    ∀ s a b : Nat,
      IsOneSplit H s → IsLeaf H a → IsLeaf H b →
      H.edge 0 s a → H.edge 0 s b →
      H.SameOneTypeBelow s a b
  one_split_witness :
    ∀ s : Nat, IsOneSplit H s → s < n →
      ∃ a b : Nat,
        a < n ∧ b < n ∧
        IsLeaf H a ∧ IsLeaf H b ∧
        s < a ∧ s < b ∧ H.oneMeetLevel a b = s
  two_split_coherent :
    ∀ s a b c d : Nat,
      IsTwoSplit H s → a < b → c < d →
      IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
      H.edge s a b → H.edge s c d →
      H.SameTwoTypeBelow s a b c d
  two_split_witness :
    ∀ s : Nat, IsTwoSplit H s → s < n →
      ∃ a b c d : Nat,
        a < b ∧ c < d ∧
        a < n ∧ b < n ∧ c < n ∧ d < n ∧
        IsLeaf H a ∧ IsLeaf H b ∧
        IsLeaf H c ∧ IsLeaf H d ∧
        s < a ∧ s < c ∧ H.twoMeetLevel a b c d = s
  leaf_marker_one :
    ∀ a b : Nat, a < b → b < n →
      IsLeaf H a → IsLeaf H b →
      (H.edge 1 a b ↔ LexEarlier H a b)
  leaf_marker_two :
    ∀ a b : Nat, a < b → b < n →
      IsLeaf H a → IsLeaf H b →
      (H.edge 2 a b ↔ ¬ LexEarlier H a b)
  permitted_edge :
    ∀ x y z : Nat, H.edge x y z → PermittedDiaryEdge H x y z

/-- Full *finite* diary: add exactly the bounded S1/S2 conditions,
without demanding impossible Devlin marker edges on the unused
infinite tail beyond n. -/
structure FiniteRoleDiaryBlock
    (H : Ordered3Graph Nat) (n : Nat) : Prop where
  prediary : FiniteRolePrediaryBlock H n
  singleton_meets :
    ∀ a b : Nat, a < b → b < n →
      IsLeaf H a → IsLeaf H b →
      IsOneSplit H (H.oneMeetLevel a b)
  pair_meets :
    ∀ a b c d : Nat, a < b → c < d →
      b < n → d < n →
      IsLeaf H a → IsLeaf H b → IsLeaf H c → IsLeaf H d →
      H.twoMeetLevel a b c d = min a c ∨
      H.twoMeetLevel a b c d = 1 ∨
      IsTwoSplit H (H.twoMeetLevel a b c d)

namespace FiniteRolePrediaryBlock

variable {H : Ordered3Graph Nat} {n : Nat}

/-- Any true marker-defined one-split lies in the finite frame. -/
theorem oneSplit_lt
    (P : FiniteRolePrediaryBlock H n)
    (s : Nat) (hs : IsOneSplit H s) : s < n :=
  (P.frame.edge_support 0 1 s hs.2.1).2.2.2

/-- Any true marker-defined two-split lies in the finite frame. -/
theorem twoSplit_lt
    (P : FiniteRolePrediaryBlock H n)
    (s : Nat) (hs : IsTwoSplit H s) : s < n :=
  (P.frame.edge_support 0 2 s hs.2.2).2.2.2

/-- A vertex at or after the finite bound is automatically a
leaf by its two absent role marker edges. -/
theorem outside_isLeaf
    (P : FiniteRolePrediaryBlock H n)
    (z : Nat) (hz : n ≤ z) (hz3 : 3 ≤ z) :
    IsLeaf H z := by
  refine ⟨hz3, ?_, ?_⟩
  · intro he
    have hlt : z < n :=
      (P.frame.edge_support 0 1 z he).2.2.2
    omega
  · intro he
    have hlt : z < n :=
      (P.frame.edge_support 0 2 z he).2.2.2
    omega

/-- Finite role coverage implies global marker-role coverage
without pretending that the global V3 or witness axioms hold. -/
theorem role_valid_global
    (P : FiniteRolePrediaryBlock H n)
    (z : Nat) (hz : 3 ≤ z) :
    IsLeaf H z ∨ IsOneSplit H z ∨ IsTwoSplit H z := by
  by_cases hzn : z < n
  · exact P.role_valid z hz hzn
  · exact Or.inl (P.outside_isLeaf z (by omega) hz)

end FiniteRolePrediaryBlock

namespace FiniteRoleDiaryBlock

variable {H : Ordered3Graph Nat} {n : Nat}

/-- Forget the two bounded S-meet clauses, keeping V/E intact. -/
theorem toPrediary
    (D : FiniteRoleDiaryBlock H n) :
    FiniteRolePrediaryBlock H n := D.prediary

end FiniteRoleDiaryBlock

end DiaryLeafPriority
end ThreeUniformDiaries
